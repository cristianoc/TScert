import { fork, type ChildProcess } from "node:child_process";
import { readFileSync, writeFileSync, rmSync } from "node:fs";
import { Socket } from "node:net";
import { availableParallelism } from "node:os";
import { basename, resolve, join } from "node:path";
import { createHash } from "node:crypto";
// ../tools/fragment-parse.mts is the trusted parser and syntactic gate: without it no source becomes the Fragment the producer and Lean read.
import { close as closeParser } from "../tools/fragment-parse.mts";
import { diagnosticsCall, parseCall, type Parsed } from "./parse-stage.mts";
import { processInconsistency, processRetirement } from "../tools/files.mts";
import { retainDeclarationSessions } from "../tools/declaration-session.mts";
import { tsconfigOf, type SeenDiagnostic } from "../tools/declaration-graph.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import { presentObligation } from "../tools/diagnostic-view.mts";
import { fieldOf, messageOf, passToolFailure } from "../tools/thrown.mts";
import { keepRunDirectories, ownedRun, requireDiskSpace, runDirectory, runRoot, withinRunDirectory } from "./run-directory.mts";
import type { Json as ParsedJson } from "../tools/calculus.mts";
import type { Ast } from "../tools/fragment.mts";
import type { SourceClaims } from "../tools/source-claims.mts";
// ../tools/source-flow.mts checks the shared execution graph wire before proposal.
import { decodeFlowDocument } from "../tools/source-flow.mts";
import { initOmission } from "../tools/fragment-parse.mts";
import { requireWellFormed, wireText } from "../tools/wire-strings.mts";
import { resolvableDeclaration } from "../tools/intrinsics.mts";
import { assemblyCall } from "./claims-assembly.mts";
import { currentStore, invokeInProcess, invokeProcess, Recorder, readInvocationLog, type AttemptRecord } from "./stages.mts";
import { producerBuild, producerCall, refusalEnd, verifierBuild, verifierCall, type ProcessCall } from "./stage-execution.mts";

/** The file of a run's directory holding its stage invocations' attempts. */
export const invocationLog = "invocations.jsonl";

/** A Fragment document this pipeline's parser wrote, read back by a test that
 * forges it. The tests (18 reads) edit fields deep in the document through
 * its type; checking those fields at each test, in place of this assertion,
 * would rewrite each of them, and no TypeScript decoder of the Fragment
 * exists. The assertion stands for the parser's output; it is not checked
 * before the test reads it. */
export function readFragmentFile(file: string): Ast {
  const parsed: ParsedJson = JSON.parse(wireText(readFileSync(file), file));
  requireWellFormed(parsed, file);
  const fragment: unknown = parsed;
  return fragment as Ast; // asserted: the parser wrote the file from an Ast; a check of every field the tests read would cost more than it guards a test's forgery
}

/** The file identity a run's Fragment names, its snapshot's path: what the
 * verifier's search and check take as the file key. */
export function sourceKey(artifacts: string): string {
  return readFragmentFile(join(artifacts, "fragment.json")).file;
}

/** A claims document this pipeline's producer wrote, read back by a test that
 * forges it. The tests (83 reads) edit fields deep in the document through
 * its type, and no TypeScript decoder of the claims exists; the assertion
 * stands for the producer's output, unchecked before the test reads it. */
export function readClaimsFile(file: string): SourceClaims {
  const parsed: ParsedJson = JSON.parse(wireText(readFileSync(file), file));
  requireWellFormed(parsed, file);
  const claims: unknown = parsed;
  return claims as SourceClaims; // asserted: the producer wrote the file against SourceClaims; a check of every field the tests read would cost more than it guards a test's forgery
}

const here = import.meta.dirname;
// The producer runs from `_build/default/producer.exe` below `../ocaml-producer`.
// Its dune file, `../ocaml-producer/dune`, declares that executable and the library it links;
// `../ocaml-producer/dune-project` makes that directory the root `dune build --root` builds into `_build/`.
export const producerExecutable: string = process.env.PRODUCER ?? producerBuild;
const repo = resolve(here, "..");
export const verifier: string = process.env.VERIFIER ?? verifierBuild;
function refusalStatus(detail: string): "exhausted" | "unverified" {
  const diagnostic = readDiagnostic(detail);
  if (!diagnostic) return "unverified";
  switch (diagnostic.outcome.kind) {
    case "exhausted": return "exhausted";
    case "not-established": return "unverified";
  }
}
export type Phase = "source" | "proposal" | "search" | "check";
export type Outcome =
  | {
      status: "verified";
      artifacts: string;
      functions: string[];
      /** The source spans of the module initialization's top-level
       * statements, which Lean checked as one unit; empty when the module
       * has no initialization code. */
      initialization: [number, number][];
      phase: "check";
      units?: UnitResult[];
    }
  | {
      status: "unsupported" | "unverified" | "exhausted" | "error";
      artifacts: string;
      detail: string;
      phase: Phase;
      /** A check of each unit's own (`checkUnits`): each unit's result, or
       * null where the file's front refused every unit. */
      units?: UnitResult[] | null;
    };
/** A check of each unit: the functions of the file read at their declared
 * signatures (`initOmission` for its initialization), and the units to
 * search and check, by a member's function name (`initOmission` for the
 * initialization), or all. */
export type UnitSelection = { omitted: string[]; select: string[] | null };
/** A unit member's name as a selection names it. */
export const memberName = (member: string): string => member === "init" ? initOmission : member.replace(/@\d+$/, "");
/** A unit's own result in a check of each unit: its identity and members as
 * the verifier's front names them (`--units`), its outcome, the phase that
 * decided it, its refusal, and, accepted, its dependencies. */
export type UnitResult = {
  unit: string;
  members: string[];
  status: "verified" | "unverified" | "exhausted" | "error";
  phase: "search" | "check";
  detail: string;
  depends: string[];
};
/** The fuel proof search is given. */
const searchDepth = 12;
/** Wall-clock limit on each external step (the producer, the lowering, the
 * search, the check): `TSCERT_STEP_LIMIT` seconds, 60 by default. A step
 * that exceeds it is killed and the case is an error naming the step and the
 * limit, never a verdict. */
export const stepTimeoutMs: number = stepLimit();
function stepLimit(): number {
  const given = process.env["TSCERT_STEP_LIMIT"];
  if (given === undefined || given === "") return 60_000;
  const seconds = Number(given);
  if (!Number.isFinite(seconds) || seconds <= 0) throw Error(`TSCERT_STEP_LIMIT is no positive number of seconds: ${given}`);
  const milliseconds = Math.round(seconds * 1000);
  if (!Number.isSafeInteger(milliseconds) || milliseconds <= 0)
    throw Error(`TSCERT_STEP_LIMIT must convert to a positive integer number of milliseconds: ${given}`);
  return milliseconds;
}
/** A step run: its exit code, its output, and what it reports on failure. */
export type Ran = { code: number; out: string; detail: string };
/** A process stage run through the common invocation mechanism, its attempt
 * recorded by `recorder`. */
export function runStep(call: ProcessCall, recorder: Recorder | null = null, limitMs: number = stepTimeoutMs): Ran {
  const p = invokeProcess(call, { limitMs, force: false, recorder });
  const step = [
    basename(call.program),
    ...call.arguments.flatMap((a) => ("text" in a && a.text.startsWith("--") ? [a.text] : [])),
  ].join(" ");
  if (p.record.execution === "timed-out")
    throw Error(
      `timeout: ${step} did not finish within ${limitMs / 1000} s`,
    );
  // A reused observation reports an earlier attempt's timeout, at a limit no
  // smaller than this one, not proof that this one would time out.
  if (p.record.execution === "timeout-replayed")
    throw Error(`timeout: ${step} did not finish within ${(p.record.replay?.stored.limitMs ?? stepTimeoutMs) / 1000} s ` +
      `(an earlier attempt, ${p.record.replay?.stored.attempt ?? "unknown"}; a longer TSCERT_STEP_LIMIT or TSCERT_RETRY_TIMEOUTS=1 runs it again)`);
  // A step killed by a signal (the verifier aborting on a stack overflow)
  // or that did not start is a failure of the tool, no verdict, reported
  // with the first line it wrote.
  if (p.error || p.signal || p.status === null) {
    const said = p.stderr.trim().split("\n")[0] ?? "";
    throw Error(`tool failure: ${step} ${p.signal ? `was killed by ${p.signal}` : "did not run"}: ` +
      `${p.error?.message ?? (said || "no exit status")}`);
  }
  // Every wire document a step prints is valid UTF-8 (`wireText`).
  const out = wireText(p.stdoutBytes, step);
  const err = wireText(p.stderrBytes, step);
  return {
    code: p.status,
    out,
    detail: err.trim() || out.trim(),
  };
}
export { refusalEnd };
/** A step's refusal record, without its end line, or null where the step
 * succeeded. A refusal is its exit status (the verifier's 1, the producer's
 * 2), a first line naming it (`reject: …`, `unsupported: …`) and a last line
 * `end of refusal`, so a record cut short is none. Any other exit but 0 (no
 * output, an exception, a usage error, a file it could not read or write,
 * the verifier's 3 and the producer's 3) is a failure of the tool, no
 * verdict. */
function refusalOf(ran: Ran, step: string, status: number, prefix: string): string | null {
  if (ran.code === 0) return null;
  const lines = ran.detail.split("\n");
  if (ran.code === status && ran.detail.startsWith(prefix) && lines.at(-1) === refusalEnd)
    return lines.slice(0, -1).join("\n").trim();
  throw Error(`tool failure: ${step} exited with status ${ran.code} without a complete refusal: ` +
    `${lines[0] || "no output"}`);
}
const verifierRefusal = (ran: Ran, step: string): string | null => refusalOf(ran, `verifier ${step}`, 1, "reject: ");
const producerRefusal = (ran: Ran): string | null => refusalOf(ran, "the producer", 2, "unsupported: ");
/** A failed search names the obligation it could not establish and why, in
 * source terms: the presentation's summary (`diagnostic-view.mts`) of the verifier's structured record, as
 * the line `obligation: …` after the verifier's own first line. Display only;
 * a record the decoder refuses adds nothing. */
function namingTheObligation(detail: string, source: string): string {
  const record = readDiagnostic(detail);
  const summary = record && presentObligation(record, source).summary;
  if (!summary) return detail;
  const [first, ...rest] = detail.split("\n");
  return [first, `obligation: ${summary}`, ...rest].join("\n");
}
/** One known cause of failure the producer met (`producer --explain`): a
 * form at a source span, and why no derivation of it is found. */
interface Explanation {
  pos: [number, number];
  reason: string;
}
/** What `JSON.parse` gives: null, a Boolean, a number, a string, a fresh
 * array or a fresh plain object of such values. */
type Json = null | boolean | number | string | readonly Json[] | JsonRecord;
type JsonRecord = { readonly [key: string]: Json };
function isJsonArray(value: Json): value is readonly Json[] {
  return Array.isArray(value);
}
function isJsonRecord(value: Json): value is JsonRecord {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
/** The producer's explanations (`producer --explain`), read field by field:
 * a run that exits otherwise than 0, or prints anything but an array of
 * `{pos, reason}` records, is a tool failure, never "no explanation". */
function readExplanations(ran: Ran): Explanation[] {
  const malformed = (what: string): Error =>
    Error(`tool failure: the producer's --explain ${what}: ${ran.detail.split("\n")[0] || "no output"}`);
  if (ran.code !== 0) throw malformed(`exited with status ${ran.code}`);
  let parsed: Json;
  try {
    parsed = JSON.parse(ran.out);
  } catch {
    throw malformed("printed no JSON");
  }
  if (!isJsonArray(parsed)) throw malformed("printed no array of explanations");
  return parsed.map((e: Json): Explanation => {
    if (!isJsonRecord(e) || Object.keys(e).sort().join() !== "pos,reason") throw malformed("printed a malformed explanation");
    const reason = e["reason"];
    const pos = e["pos"];
    const [start, end] = isJsonArray(pos) && pos.length === 2 ? pos : [];
    if (typeof reason !== "string" || typeof start !== "number" || typeof end !== "number")
      throw malformed("printed a malformed explanation");
    return { pos: [start, end], reason };
  });
}
/** A search that found no derivation, or a quantified call it could not show
 * within its bound or resolution qualification, is refused by name where its cause is
 * known, on a first line of its own before the verifier's, which follow
 * unchanged: the producer's explanation of a form at the failed obligation
 * (the innermost whose span meets the obligation's), else, for code
 * TypeScript refuses, where the caller asks for it (`--typescript-errors`: it
 * loads the project again, a second of CPU), the TypeScript error nearest
 * the failed obligation: the pipeline follows TypeScript's types. Display only: the outcome is the same unverified search,
 * which Lean decided on the ordinary proposal. */
function refusedByName(detail: string, explain: () => Explanation[],
    read: () => SeenDiagnostic[]): string {
  if (!detail.includes("evidence search failed") &&
      !detail.includes("does not satisfy the closure's bound") &&
      !detail.includes("resolution certificate does not establish")) return detail;
  const at = /at \[(\d+),(\d+)\)/.exec(detail);
  if (at) {
    const [start, end] = [Number(at[1]), Number(at[2])];
    const meets = explain().filter((e) => e.pos[0] < Math.max(end, start + 1) && start < e.pos[1])
      .sort((a, b) => (a.pos[1] - a.pos[0]) - (b.pos[1] - b.pos[0]));
    if (meets.length) return `reject: ${meets[0].reason}\n${detail}`;
  }
  const errors = read();
  if (!errors.length) return detail;
  const pos = at ? Number(at[1]) : 0;
  const distance = (d: SeenDiagnostic) =>
    pos < d.pos[0] ? d.pos[0] - pos : pos > d.pos[1] ? pos - d.pos[1] : 0;
  const nearest = errors.reduce((a, b) => (distance(b) < distance(a) ? b : a));
  const text = nearest.text.split("\n")[0];
  return `reject: TypeScript refuses this code too (line ${nearest.start.line + 1}, col ${
    nearest.start.character + 1}: ${text}); the pipeline follows TypeScript's types\n${detail}`;
}
/** A refusal of the gate or the producer, which names no obligation, is
 * refused by name where TypeScript refuses the code too (`--typescript-errors`):
 * the first TypeScript error of the checked file, on a first line of its own
 * before the refusal, which follows unchanged. The pipeline follows
 * TypeScript's types, and a program TypeScript rejects has none to follow.
 * Display only: the outcome is the same refusal. */
function refusedByTypeScript(detail: string, read: () => SeenDiagnostic[]): string {
  // An import TypeScript does not resolve says where the file was put, not
  // what its code does.
  const errors = read().filter((d) => !d.text.startsWith("Cannot find module"));
  if (!errors.length) return detail;
  const first = errors.reduce((a, b) => (b.pos[0] < a.pos[0] ? b : a));
  return `reject: TypeScript refuses this code too (line ${first.start.line + 1}, col ${
    first.start.character + 1}: ${first.text.split("\n")[0]}); the pipeline follows TypeScript's types\n${detail}`;
}
/** The TypeScript diagnostics stage: the errors TypeScript reports for
 * `file` in its project, an observed stage. */
export function typeScriptErrors(recorder: Recorder, file: string, tsconfigPath?: string): SeenDiagnostic[] {
  return invokeInProcess(diagnosticsCall(file, tsconfigPath), { force: false, recorder }).value;
}
/** A field of a parsed document, `undefined` where it has none. */
const field = (value: unknown, key: string): unknown => fieldOf(value, key);
const list = (value: unknown): unknown[] => (Array.isArray(value) ? value : []);
const spanOf = (value: unknown): [number, number] | null =>
  Array.isArray(value) && value.length === 2 && typeof value[0] === "number" && typeof value[1] === "number"
    ? [value[0], value[1]] : null;
/** A read of an import the pipeline proposes qualified (certified imports):
 * the reading document's name of it, its declaration identity, its module,
 * and its unit's claimed footprint and on-throw flag. */
type QualifiedRead = { local: string; declaration: unknown; module: string; name: string;
  footprint: unknown; onThrow: boolean };
/** A module's claims, kept as text: a bigint literal's digits pass through
 * unrounded. */
type ModuleClaims = { text: string; parsed: unknown };
/** The reads of a document's imported values that may be qualified: a named
 * function import whose declaration is a unit of a module with claims, both
 * readings eligible as Lean requires them (`planImports`), and not
 * withdrawn (`module#name`, or `module#*` for all of a module's). */
function eligibleReads(declarations: unknown, units: Map<string, unknown[]>, claims: Map<string, ModuleClaims>,
    withdrawn: Set<string>): QualifiedRead[] {
  return list(field(declarations, "values")).flatMap((v): QualifiedRead[] => {
    const declaration = field(v, "declaration"), type = field(v, "type"), local = field(field(v, "binding"), "local");
    const module = field(declaration, "module"), name = field(declaration, "name");
    const span = spanOf(field(declaration, "span"));
    if (typeof module !== "string" || typeof name !== "string" || typeof local !== "string" || !span) return [];
    if (withdrawn.has(`${module}#${name}`) || withdrawn.has(`${module}#*`)) return [];
    if (field(v, "construct") !== false || list(field(v, "typeParams")).length > 0 || field(type, "k") !== "function" ||
        field(type, "rest") !== null || field(type, "receiver") !== null ||
        field(field(type, "effect"), "promise") !== null) return [];
    const unit = (units.get(module) ?? []).find((f) => {
      const at = spanOf(field(f, "namePos"));
      return field(f, "name") === name && !!at && span[0] <= at[0] && at[1] <= span[1];
    });
    if (!unit || list(field(unit, "typeParams")).length > 0 || field(unit, "guard") !== null ||
        list(field(unit, "params")).some((p) => field(p, "rest") !== undefined || field(p, "name") === "this")) return [];
    const at = spanOf(field(unit, "namePos"));
    const claimed = list(field(claims.get(module)?.parsed, "functions")).find((f) => {
      const p = spanOf(field(f, "namePos"));
      return field(f, "name") === name && !!p && !!at && p[0] === at[0] && p[1] === at[1];
    });
    const onThrow = field(claimed, "onThrow");
    if (!claimed || typeof onThrow !== "boolean") return [];
    return [{ local, declaration, module, name, footprint: field(claimed, "footprint"), onThrow }];
  });
}
/** Propose a document's claims, its eligible reads qualified. */
function propose(recorder: Recorder, ast: string, flow: string, reads: QualifiedRead[], qualifiedPath: string): Ran {
  writeFileSync(qualifiedPath, JSON.stringify(reads.map(({ local, declaration, footprint, onThrow }) =>
    ({ local, declaration, footprint, onThrow }))));
  return runStep(producerCall(producerExecutable, reads.length ? [ast, flow, qualifiedPath] : [ast, flow]), recorder);
}
/**
 * The modules of the fragment, each a run of its own: its document,
 * standalone, lowered once and proposed as a file is, at its own eligible
 * reads. A module is proposed after the modules it imports from, so a read
 * may name only a module proposed before it: one closing a cycle of imports
 * is read at its ordinary signature. A module whose lowering or proposal
 * fails is left out.
 */
class ModuleRuns {
  private readonly docs = new Map<string, { index: number; ast: string; flow: string; declarations: unknown;
    imports: string[] }>();
  private readonly units = new Map<string, unknown[]>();
  private readonly proposed = new Map<string, ModuleClaims | null>();
  private readonly artifacts: string;
  private readonly recorder: Recorder;
  constructor(recorder: Recorder, artifacts: string, fragment: unknown) {
    this.artifacts = artifacts;
    this.recorder = recorder;
    const locations = list(field(fragment, "modules")).map((m) => field(m, "location"));
    for (const [index, m] of list(field(fragment, "modules")).entries()) {
      const location = field(m, "location");
      if (typeof location !== "string") continue;
      const doc = { file: location, sourceSha256: field(m, "sourceSha256"), declarations: field(m, "declarations"),
        init: field(m, "init"), functions: field(m, "functions"), modules: [] };
      const ast = join(artifacts, `module-${index}.fragment.json`);
      writeFileSync(ast, JSON.stringify(doc));
      const lowered = runStep(verifierCall(verifier, ["--lower-control-flow", ast]), recorder);
      // A module the verifier refuses to lower is read at its declared types.
      if (verifierRefusal(lowered, "--lower-control-flow") !== null) continue;
      const flow = join(artifacts, `module-${index}.flow.json`);
      writeFileSync(flow, JSON.stringify(decodeFlowDocument(JSON.parse(lowered.out))));
      const imports = [...new Set(list(field(doc.declarations, "values")).map((v) => field(field(v, "declaration"), "module"))
        .filter((l): l is string => typeof l === "string" && l !== location && locations.includes(l)))];
      this.docs.set(location, { index, ast, flow, declarations: doc.declarations, imports });
      this.units.set(location, list(field(m, "functions")));
    }
  }
  /** Each module's claims, and the reads of each module's claims, at the
   * reads not withdrawn; then the importer's eligible reads. */
  claims(declarations: unknown, withdrawn: Set<string>): { claims: Map<string, ModuleClaims>;
      readsOf: Map<string, QualifiedRead[]>; reads: QualifiedRead[] } {
    const claims = new Map<string, ModuleClaims>();
    const readsOf = new Map<string, QualifiedRead[]>();
    const visiting = new Set<string>();
    const visit = (location: string): void => {
      const doc = this.docs.get(location);
      if (!doc || visiting.has(location) || readsOf.has(location)) return;
      visiting.add(location);
      for (const l of doc.imports) visit(l);
      visiting.delete(location);
      const reads = eligibleReads(doc.declarations, this.units, claims, withdrawn);
      readsOf.set(location, reads);
      const key = `${location}\n${JSON.stringify(reads)}`;
      if (!this.proposed.has(key)) {
        const proposed = propose(this.recorder, doc.ast, doc.flow, reads,
          join(this.artifacts, `module-${doc.index}.qualified.json`));
        writeFileSync(join(this.artifacts, `module-${doc.index}.proposal.log`), proposed.detail);
        // A module the producer refuses is read at its declared types.
        this.proposed.set(key, producerRefusal(proposed) !== null ? null : { text: proposed.out, parsed: JSON.parse(proposed.out) });
      }
      const proposed = this.proposed.get(key);
      if (proposed) claims.set(location, proposed);
    };
    for (const location of this.docs.keys()) visit(location);
    return { claims, readsOf, reads: eligibleReads(declarations, this.units, claims, withdrawn) };
  }
}
/** The modules whose claims `reads` need, through the modules' own reads. */
function readClosure(reads: QualifiedRead[], readsOf: Map<string, QualifiedRead[]>): string[] {
  const seen: string[] = [];
  for (let work = reads.map((r) => r.module), next = work.shift(); next !== undefined; next = work.shift()) {
    if (seen.includes(next)) continue;
    seen.push(next);
    work.push(...(readsOf.get(next) ?? []).map((r) => r.module));
  }
  return seen;
}
/** The first certified import a failed search or check names, as Lean names
 * it: a qualified read (`certified import <module>#<name>: …`), or a module
 * run (`module <module>: …`). */
function failedImport(detail: string): { module: string; name: string | null } | null {
  const read = /certified import (\S+)#([^:\s]+): /.exec(detail);
  if (read?.[1] && read[2]) return { module: read[1], name: read[2] };
  const run = /module (\S+): /.exec(detail);
  return run?.[1] ? { module: run[1], name: null } : null;
}

/** The reads and module runs the plan of `reads` refuses, before the
 * importer is proposed at them, each as `module#name` or `module#*`: the
 * plan (`--plan-imports`) states each read it refuses on a line of its own,
 * and all of them are withdrawn in one round. Empty where the plan holds or
 * its refusal names none. The plan reads of the importer's claims document
 * only its `qualified` list, which the producer writes as the declarations
 * of `reads`, in order, and its `modules`, the claims `used`: given those,
 * its answer is the one the search of the assembled claims gives. */
function planRefused(recorder: Recorder, ast: string, reads: QualifiedRead[], used: string[], budget: string[],
    planPath: string): string[] {
  // Spliced as text, as the claims assembly is: a bigint literal's digits pass through unrounded.
  writeFileSync(planPath, `{"qualified":${JSON.stringify(reads.map((r) => r.declaration))},"modules":[${used.join(",")}]}`);
  const refusal = verifierRefusal(runStep(verifierCall(verifier, [...budget, "--plan-imports", ast, planPath]), recorder),
    "--plan-imports");
  return [...new Set((refusal ?? "").split("\n").flatMap((line) => {
    const failed = failedImport(line);
    return failed ? [`${failed.module}#${failed.name ?? "*"}`] : [];
  }))];
}

/** The parse stage of `source`, read in the project `tsconfigPath` (or a
 * snapshot's own), its log and the TypeScript errors its gate read written
 * under `artifacts`: the parse, the source's bytes, the snapshot it parsed and the file its
 * imports resolve as. */
export function parseSource(source: string, tsconfigPath: string | undefined, artifacts: string, recorder: Recorder,
    omitted: readonly string[] = []): { parsed: Parsed; bytes: Buffer; snapshot: string; resolution: string } {
  // Parse a snapshot, not a path whose contents may change during verification.
  const bytes = readFileSync(resolve(source));
  const configuration = Buffer.from(JSON.stringify({
    compilerOptions: { strict: true, noEmit: true, target: "es2022" },
    files: ["source.ts", resolvableDeclaration],
  }));
  writeFileSync(join(artifacts, "source.ts"), bytes);
  writeFileSync(join(artifacts, "tsconfig.json"), configuration);
  // The snapshot's path is the Fragment's file identity, which every later
  // stage's input embeds: with the store, it is a stable location named by
  // the snapshot's and its configuration's contents, the same in every run;
  // where the store gives none (a pass is removing snapshots), the run's copy.
  const snapshot = join(currentStore()?.stableDirectory("sources", [["source.ts", bytes],
    ["tsconfig.json", configuration]]) ?? artifacts, "source.ts");
  // A caller may name the TypeScript project the source belongs to. The
  // snapshot is parsed, and TypeScript resolves its imports as the original
  // file in that project; the parser requires both to have the same bytes.
  // The producer and verifier still decide whether they can interpret the
  // declarations reached.
  const resolution = tsconfigPath ? resolve(source) : snapshot;
  // The parse stage, an observed stage.
  const parsed = invokeInProcess(parseCall(bytes, snapshot, tsconfigPath, resolution, omitted), { force: false, recorder }).value;
  // The TypeScript errors the parser's gate read are kept beside its log,
  // accepted or not: they are where a refusal over one of them points.
  writeFileSync(join(artifacts, "typescript-diagnostics.json"), JSON.stringify(parsed.seen, null, 1) + "\n");
  writeFileSync(join(artifacts, "parse.log"), parsed.detail);
  return { parsed, bytes, snapshot, resolution };
}

/** A failed job carries its invocation log after its directory is removed. */
export class RunFailure extends Error {
  readonly invocations: AttemptRecord[];
  constructor(reason: string, invocations: AttemptRecord[]) {
    super(reason);
    this.invocations = invocations;
  }
}
function failedRun(artifacts: string, reason: string): RunFailure {
  try {
    return new RunFailure(reason, readInvocationLog(join(artifacts, invocationLog)));
  } finally {
    rmSync(artifacts, { recursive: true, force: true });
  }
}

/** One round of a check of each unit: the search of the file's selected
units (`--produce-units`) and their check (`--check-units`), each over the
file's one front. Where the search of the file does not finish within its
limit, each unit is searched and checked on its own, so the limit is each
unit's. A refusal naming a certified import asks for that import's
withdrawal; a refused front refuses every unit. */
function unitRound(recorder: Recorder, artifacts: string, ast: string, claims: string, snapshot: string,
    budget: string[], select: string[] | null): { withdraw: string } | { front: string } | { results: UnitResult[] } {
  const named = select === null ? [] : [select.join(",")];
  const search = (evidence: string, names: string[]): { refused: Map<string, string>; front: string | null } => {
    const produced = runStep(verifierCall(verifier, [...budget, "--produce-units", ast, claims, snapshot, evidence,
      String(searchDepth), ...names]), recorder);
    writeFileSync(join(artifacts, "search.log"), produced.detail);
    const refusal = verifierRefusal(produced, "--produce-units");
    const lines = produced.out.split("\n");
    if (refusal !== null && !lines.some((l) => l.startsWith("checked source evidence written: ")))
      return { refused: new Map(), front: refusal };
    return { front: null, refused: new Map(lines.filter((l) => l.startsWith("refused: ")).map((l): [string, string] => {
      const value: unknown = JSON.parse(l.slice("refused: ".length));
      const unit = field(value, "unit"), detail = field(value, "refusal");
      if (typeof unit !== "string" || typeof detail !== "string")
        throw Error("tool failure: verifier --produce-units printed a malformed refusal");
      return [unit, detail];
    })) };
  };
  const strings = (value: unknown): string[] => {
    if (!Array.isArray(value) || !value.every((x): x is string => typeof x === "string"))
      throw Error("tool failure: verifier listed a unit without its members or dependencies");
    return value;
  };
  const check = (evidence: string, names: string[], refused: Map<string, string>): UnitResult[] | string => {
    const checked = runStep(verifierCall(verifier, [...budget, "--check-units", ast, claims, snapshot, evidence, ...names]),
      recorder);
    writeFileSync(join(artifacts, "check.log"), checked.detail);
    const verdicts = checked.out.split("\n").filter((l) => l.startsWith("{"));
    const refusal = verifierRefusal(checked, "--check-units");
    if (refusal !== null && verdicts.length === 0) return refusal;
    return verdicts.map((line): UnitResult => {
      const value: unknown = JSON.parse(line);
      const unit = field(value, "unit"), members = strings(field(value, "members"));
      if (typeof unit !== "string") throw Error("tool failure: verifier --check-units printed a verdict without its unit");
      if (field(value, "accepted") === true)
        return { unit, members, status: "verified", phase: "check", detail: "", depends: strings(field(value, "depends")) };
      const searchRefusal = refused.get(unit);
      const reason = searchRefusal ?? field(value, "refusal");
      if (typeof reason !== "string") throw Error("tool failure: verifier --check-units printed a verdict without its refusal");
      // A unit's refusal reads as the verifier's refusal of a command does.
      const detail = `reject: ${reason}`;
      return { unit, members, status: refusalStatus(detail), phase: searchRefusal !== undefined ? "search" : "check",
        detail, depends: [] };
    });
  };
  const withdrawal = (results: UnitResult[]): { withdraw: string } | null => {
    for (const r of results) {
      const failed = r.status === "verified" ? null : failedImport(r.detail);
      if (failed) return { withdraw: `${failed.module}#${failed.name ?? "*"}` };
    }
    return null;
  };
  const evidence = join(artifacts, "evidence.json");
  let results: UnitResult[];
  try {
    const searched = search(evidence, named);
    if (searched.front !== null) {
      const failed = failedImport(searched.front);
      return failed ? { withdraw: `${failed.module}#${failed.name ?? "*"}` } : { front: searched.front };
    }
    const checked = check(evidence, named, searched.refused);
    if (typeof checked === "string") {
      const failed = failedImport(checked);
      return failed ? { withdraw: `${failed.module}#${failed.name ?? "*"}` } : { front: checked };
    }
    results = checked;
  } catch (error) {
    if (!messageOf(error).startsWith("timeout: ")) throw error;
    // Each unit on its own: the units as the front lists them, each searched and checked by its first member's name.
    const listed = runStep(verifierCall(verifier, [...budget, "--units", ast, claims, snapshot, ...named]), recorder);
    const front = verifierRefusal(listed, "--units");
    if (front !== null) return { front };
    results = [];
    for (const [index, line] of listed.out.split("\n").filter((l) => l !== "").entries()) {
      const value: unknown = JSON.parse(line);
      const unit = field(value, "unit"), members = strings(field(value, "members"));
      if (typeof unit !== "string") throw Error("tool failure: verifier --units listed a unit without its identity");
      const first = members[0];
      // A module run is checked with every unit of its file.
      if (first === undefined) continue;
      const own = join(artifacts, `unit-${index}.evidence.json`);
      try {
        const searched = search(own, [memberName(first)]);
        const checked = searched.front ?? check(own, [memberName(first)], searched.refused);
        if (typeof checked === "string")
          results.push({ unit, members, status: refusalStatus(checked), phase: "search", detail: checked, depends: [] });
        else results.push(...checked.filter((r) => r.unit === unit || (r.unit.startsWith("module:") &&
          !results.some((x) => x.unit === r.unit))));
      } catch (unitError) {
        results.push({ unit, members, status: "error", phase: "search", detail: messageOf(unitError), depends: [] });
      }
    }
  }
  return withdrawal(results) ?? { results };
}

/** A completed run releases its artifacts. A file consumer requests retention
 * and uses `using result = check(...)` to release them after consumption. */
export function check(source: string, tsconfigPath?: string, typescriptErrors: boolean = false,
    subtypeRounds?: number, retainArtifacts: boolean = false, units: UnitSelection = { omitted: [], select: null }):
    Outcome & Disposable {
  const artifacts = runDirectory("pipeline-");
  try {
    return ownedRun(checkUnowned(artifacts, source, tsconfigPath, typescriptErrors, subtypeRounds, units), retainArtifacts);
  } catch (error) {
    throw failedRun(artifacts, messageOf(error));
  }
}

/** Acceptance is deliberately private to this module. A proposal alone cannot
 * construct the public verified outcome: both Lean phases must succeed. */
function checkUnowned(artifacts: string, source: string, tsconfigPath?: string, typescriptErrors: boolean = false,
    subtypeRounds?: number, units: UnitSelection = { omitted: [], select: null }): Outcome {
  using directoryScope = withinRunDirectory(artifacts);
  // Every stage invocation's attempt, in order (`stages.mts`).
  const recorder = new Recorder(join(artifacts, invocationLog));
  // What the run was asked, beside its stage invocation log.
  writeFileSync(join(artifacts, "request.json"), JSON.stringify({ source: resolve(source), project: tsconfigPath ?? null }));
  let phase: Phase = "source";
  try {
    if (subtypeRounds !== undefined && (!Number.isSafeInteger(subtypeRounds) || subtypeRounds < 0))
      throw Error("subtype rounds must be a natural number");
    const { parsed, bytes, snapshot, resolution } = parseSource(source, tsconfigPath, artifacts, recorder, units.omitted);
    const refusedErrors = () =>
      typescriptErrors
        ? typeScriptErrors(recorder, resolution, tsconfigPath)
        : [];
    if (parsed.code !== 0)
      return parsed.detail.startsWith("gate:")
        ? { status: "unsupported", artifacts, phase, detail: refusedByTypeScript(parsed.detail, refusedErrors) }
        : { status: "error", artifacts, phase, detail: parsed.detail };
    const ast = join(artifacts, "fragment.json");
    writeFileSync(ast, parsed.out);
    const parsedData: unknown = JSON.parse(parsed.out);
    if (
      !parsedData ||
      typeof parsedData !== "object" ||
      !("sourceSha256" in parsedData) ||
      parsedData.sourceSha256 !==
        createHash("sha256").update(bytes).digest("hex")
    )
      throw Error("parser fingerprint differs from source snapshot");
    if (!("functions" in parsedData) || !Array.isArray(parsedData.functions))
      throw Error("parser omitted functions");
    const functions = parsedData.functions.map((f: unknown) => {
      if (
        !f ||
        typeof f !== "object" ||
        !("name" in f) ||
        typeof f.name !== "string"
      )
        throw Error("invalid function identity");
      return f.name;
    });
    if (!("init" in parsedData) || !Array.isArray(parsedData.init))
      throw Error("parser omitted the module initialization");
    const initialization = parsedData.init.map((s: unknown): [number, number] => {
      if (!s || typeof s !== "object" || !("pos" in s) || !Array.isArray(s.pos) ||
          s.pos.length !== 2 || !s.pos.every((n: unknown) => typeof n === "number"))
        throw Error("invalid initialization statement position");
      return [s.pos[0], s.pos[1]];
    });
    const flow = join(artifacts, "flow.json");
    const lowered = runStep(verifierCall(verifier, ["--lower-control-flow", ast]), recorder);
    writeFileSync(join(artifacts, "flow.log"), lowered.detail);
    const loweringRefusal = verifierRefusal(lowered, "--lower-control-flow");
    if (loweringRefusal !== null)
      return { status: "unsupported", artifacts, phase, detail: loweringRefusal };
    writeFileSync(flow, JSON.stringify(decodeFlowDocument(JSON.parse(lowered.out))));
    phase = "proposal";
    // Certified imports: each module's claims, and the reads they may
    // qualify. A read the search or the check refuses, or a module run it
    // refuses, is withdrawn, and the documents proposed again without it.
    // A document with qualified reads is searched run by run
    // (`searchRuns`), so a later round replays the runs it leaves unchanged.
    const modules = new ModuleRuns(recorder, artifacts, parsedData);
    const withdrawn = new Set<string>();
    const claims = join(artifacts, "claims.json");
    const budget = subtypeRounds === undefined ? [] : ["--subtype-rounds", String(subtypeRounds)];
    for (;;) {
      phase = "proposal";
      const { claims: moduleClaims, readsOf, reads } = modules.claims(field(parsedData, "declarations"), withdrawn);
      // The claims of each module a read qualifies, directly or through a
      // module's reads.
      const used = readClosure(reads, readsOf).flatMap((m) => {
        const text = moduleClaims.get(m)?.text;
        return text === undefined ? [] : [text];
      });
      // The reads the plan refuses are withdrawn before the importer is
      // proposed at them: the plan reads of the importer's claims only the qualified
      // reads, which the proposal lists as `reads` (`planRefused`).
      const refused = reads.length > 0 ? planRefused(recorder, ast, reads, used, budget, join(artifacts, "plan-reads.json")) : [];
      const fresh = refused.filter((r) => !withdrawn.has(r));
      if (fresh.length > 0) {
        for (const r of fresh) withdrawn.add(r);
        continue;
      }
      const proposed = propose(recorder, ast, flow, reads, join(artifacts, "qualified.json"));
      writeFileSync(join(artifacts, "proposal.log"), proposed.detail);
      const proposalRefusal = producerRefusal(proposed);
      if (proposalRefusal !== null)
        return { status: "unsupported", artifacts, phase, detail: refusedByTypeScript(proposalRefusal, refusedErrors) };
      // The importer's claims, its `modules` the claims `used`.
      const assembled = invokeInProcess(assemblyCall(proposed.out, used), { force: false, recorder }).value;
      writeFileSync(claims, assembled);
      phase = "search";
      const round = unitRound(recorder, artifacts, ast, claims, snapshot, budget, units.select);
      if ("withdraw" in round) {
        if (withdrawn.has(round.withdraw)) return { status: "error", artifacts, phase,
          detail: `a refusal names the certified import ${round.withdraw} again after its withdrawal`, units: null };
        withdrawn.add(round.withdraw);
        continue;
      }
      if ("front" in round)
        return { status: refusalStatus(round.front), artifacts, phase, detail: round.front, units: null };
      const first = round.results.find((u) => u.status !== "verified");
      if (first === undefined)
        return { status: "verified", artifacts, phase: "check", functions, initialization, units: round.results };
      // The file's refusal is its first unit's, a search's named as a whole-file search names it.
      const detail = first.phase === "search" && first.status !== "error"
        ? refusedByName(namingTheObligation(first.detail, bytes.toString("utf8")),
          () => readExplanations(runStep(producerCall(producerExecutable, ["--explain", ast, flow]), recorder)),
          refusedErrors)
        : first.detail;
      return { status: first.status === "verified" ? "error" : first.status, artifacts, phase: first.phase,
        detail, units: round.results };
    }
  } catch (e) {
    return {
      status: "error",
      artifacts,
      phase,
      detail: messageOf(e),
    };
  }
}
const phases: readonly Phase[] = ["source", "proposal", "search", "check"];
const isPhase = (value: unknown): value is Phase => phases.some((p) => p === value);
const isSpan = (value: unknown): value is [number, number] =>
  Array.isArray(value) && value.length === 2 && value.every((n: unknown) => typeof n === "number");
/** The outcome a run in a process of its own printed, read field by field;
 * anything else is refused. */
export function readOutcome(value: unknown): Outcome {
  if (!value || typeof value !== "object" || !("status" in value) || !("artifacts" in value) ||
      !("phase" in value) || typeof value.artifacts !== "string" || !isPhase(value.phase))
    throw Error("not an outcome");
  const { status, artifacts, phase } = value;
  const units = "units" in value ? value.units : undefined;
  if (status === "verified" && phase === "check" && "functions" in value && Array.isArray(value.functions) &&
      value.functions.every((f: unknown) => typeof f === "string") && "initialization" in value &&
      Array.isArray(value.initialization) && value.initialization.every(isSpan))
    return { status, artifacts, phase, functions: value.functions, initialization: value.initialization,
      ...(units === undefined ? {} : { units: readUnitResults(units) }) };
  if ((status === "unsupported" || status === "unverified" || status === "exhausted" || status === "error") &&
      "detail" in value && typeof value.detail === "string")
    return { status, artifacts, phase, detail: value.detail,
      ...(units === undefined ? {} : { units: units === null ? null : readUnitResults(units) }) };
  throw Error("not an outcome");
}
const unitStatuses: readonly UnitResult["status"][] = ["verified", "unverified", "exhausted", "error"];
/** A list of unit results, read field by field. */
function readUnitResults(value: unknown): UnitResult[] {
  if (!Array.isArray(value)) throw Error("not an outcome: its units are no list");
  const strings = (x: unknown): string[] | null =>
    Array.isArray(x) && x.every((s): s is string => typeof s === "string") ? x : null;
  return value.map((u: unknown): UnitResult => {
    const unit = field(u, "unit"), members = strings(field(u, "members")), status = unitStatuses.find((s) => s === field(u, "status"));
    const phase = field(u, "phase"), detail = field(u, "detail"), depends = strings(field(u, "depends"));
    if (typeof unit !== "string" || !members || !status || (phase !== "search" && phase !== "check") ||
        typeof detail !== "string" || !depends)
      throw Error("not an outcome: a unit result is malformed");
    return { unit, members, status, phase, detail, depends };
  });
}
/** What one check is asked: the arguments of `check`, as they cross to a worker. */
type Request = { artifacts: string; source: string; project?: string; typescriptErrors: boolean; subtypeRounds?: number;
  retainArtifacts: boolean; units: UnitSelection };
function readRequest(value: unknown): Request {
  if (!value || typeof value !== "object" || !("source" in value) || typeof value.source !== "string" ||
      !("artifacts" in value) || typeof value.artifacts !== "string" ||
      !("typescriptErrors" in value) || typeof value.typescriptErrors !== "boolean" ||
      !("retainArtifacts" in value) || typeof value.retainArtifacts !== "boolean")
    throw Error("not a request");
  const project = "project" in value && typeof value.project === "string" ? value.project : undefined;
  const subtypeRounds = "subtypeRounds" in value && typeof value.subtypeRounds === "number"
    ? value.subtypeRounds : undefined;
  const given = "units" in value ? value.units : null;
  const strings = (x: unknown): string[] | null =>
    Array.isArray(x) && x.every((u): u is string => typeof u === "string") ? x : null;
  const omitted = strings(field(given, "omitted")), select = field(given, "select");
  if (!omitted || !(select === null || strings(select))) throw Error("not a request");
  const units: UnitSelection = { omitted, select: select === null ? null : strings(select) };
  return { artifacts: value.artifacts, source: value.source, project, typescriptErrors: value.typescriptErrors, subtypeRounds,
    retainArtifacts: value.retainArtifacts, units };
}
const checkRequest = (r: Request): Outcome =>
  checkUnowned(r.artifacts, r.source, r.project ? tsconfigOf(r.project) : undefined, r.typescriptErrors, r.subtypeRounds,
    r.units);

/** A whole check is killed after this long: the parser runs inside the worker,
 * so its step has no limit of its own. */
const checkTimeoutMs = 4 * stepTimeoutMs;
type Job = { request: Omit<Request, "artifacts">; done: (o: Outcome) => void; fail: (e: Error) => void };
const queue: Job[] = [];
const idle: ChildProcess[] = [];
/** The workers that answer their current check and exit: their caches may
 * disagree with the file system (STAGE-STORE.md, "Observed stages"). */
const retiring = new WeakSet<ChildProcess>();
const retiringMessage = "retiring";
const logs = new Map<ChildProcess, string>();
let workers: number = 0;
/** Give queued checks to idle workers, starting one per core at most. An idle
 * worker does not keep the caller's process alive. */
function dispatch(): void {
  for (let job = queue.shift(); job; job = queue.shift()) {
    const worker = idle.pop() ?? (workers < availableParallelism() ? startWorker() : undefined);
    if (!worker) {
      queue.unshift(job);
      return;
    }
    give(worker, job);
  }
}
function startWorker(): ChildProcess {
  workers++;
  // The workers write their runs under the caller's root, which outlives them.
  runRoot();
  const worker = fork(import.meta.filename, ["--serve"], { cwd: repo, stdio: ["ignore", "ignore", "pipe", "ipc"], detached: true });
  // What the worker writes to standard error is shown only with a failure.
  worker.stderr?.setEncoding("utf8");
  worker.stderr?.on("data", (text: unknown) => { logs.set(worker, (logs.get(worker) ?? "") + String(text)); });
  if (worker.stderr instanceof Socket) worker.stderr.unref();
  worker.on("exit", () => {
    stopWorker(worker);
    workers--;
    const at = idle.indexOf(worker);
    if (at >= 0) idle.splice(at, 1);
    dispatch();
  });
  return worker;
}
/** A worker owns its process group. Killing its stage runners also closes
 * their watchdog pipes, which stop the stages' separate process groups. */
function stopWorker(worker: ChildProcess): void {
  if (process.platform !== "win32" && worker.pid !== undefined) {
    try {
      process.kill(-worker.pid, "SIGKILL");
      return;
    } catch {
      // The group can already be gone after an ordinary worker exit.
    }
  }
  worker.kill("SIGKILL");
}
function give(worker: ChildProcess, job: Job): void {
  const artifacts = runDirectory("pipeline-");
  let timedOut = false;
  const fail = (reason: string): void => job.fail(failedRun(artifacts, reason));
  logs.set(worker, "");
  // A check in flight keeps the caller alive until its worker's `close`:
  // the worker's exit can precede it, while a process of the worker's group
  // still holds its standard error.
  worker.ref();
  worker.channel?.ref();
  if (worker.stderr instanceof Socket) worker.stderr.ref();
  const settle = (finish: () => void) => {
    clearTimeout(timer);
    worker.off("message", answered);
    worker.off("close", died);
    finish();
  };
  const answered = (message: unknown) => {
    // A worker retiring says so before its outcome, and takes no more checks.
    if (message === retiringMessage) {
      retiring.add(worker);
      return;
    }
    finished(message);
  };
  const finished = (message: unknown) => settle(() => {
    worker.unref();
    worker.channel?.unref();
    if (worker.stderr instanceof Socket) worker.stderr.unref();
    if (!retiring.has(worker)) idle.push(worker);
    try {
      job.done(readOutcome(message));
    } catch (error) {
      fail(`no outcome: ${messageOf(error)} ${logs.get(worker)?.trim() ?? ""}`);
    }
    dispatch();
  });
  const died = () => settle(() => fail(timedOut
    ? `timeout: ${basename(job.request.source)} did not finish within ${checkTimeoutMs / 1000} s`
    : `no outcome: the worker for ${job.request.source} exited: ${logs.get(worker)?.trim() ?? ""}`));
  // A check whose search runs each unit on its own is bounded by its steps' limits alone.
  const timer = job.request.units.select !== null ? undefined : setTimeout(() => {
    timedOut = true;
    stopWorker(worker);
  }, checkTimeoutMs);
  worker.on("message", answered);
  worker.on("close", died);
  // A worker that ended before the request reaches it fails the write; its
  // `close` reports the check.
  worker.send({ ...job.request, artifacts }, () => {});
}
/** The same check in one of a pool of worker processes, one per core, each
 * keeping its compiler between checks: for a caller that must stay responsive
 * or runs several at once. `project` is what `--project` takes;
 * `typescriptErrors`, whether a failed search is named by TypeScript's errors
 * (`--typescript-errors`). */
export function checkApart(source: string, project?: string, typescriptErrors: boolean = false,
    subtypeRounds?: number, retainArtifacts: boolean = false, units: UnitSelection = { omitted: [], select: null }):
    Promise<Outcome & Disposable> {
  runRoot();
  requireDiskSpace();
  return new Promise<Outcome>((done, fail) => {
    queue.push({ request: { source, project, typescriptErrors, subtypeRounds, retainArtifacts, units }, done, fail });
    dispatch();
  }).then(result => ownedRun(result, retainArtifacts));
}
// A worker of `checkApart`'s pool: one check per message, answered with its outcome.
if (process.argv[1] && resolve(process.argv[1]) === import.meta.filename && process.argv[2] === "--serve") {
  // A worker keeps one declaration session between its checks (STAGE-STORE.md,
  // "Retained declaration sessions"), released when it ends.
  retainDeclarationSessions(true);
  const end: (code: number) => never = (code) => {
    retainDeclarationSessions(false);
    closeParser();
    process.exit(code);
  };
  process.on("message", (message: unknown) => {
    let outcome: Outcome;
    try {
      outcome = checkRequest(readRequest(message));
    } catch (error) {
      process.stderr.write(messageOf(error) + "\n");
      end(1);
    }
    // A process whose caches may disagree with the file system answers
    // this check and exits: a fresh worker takes the next (STAGE-STORE.md,
    // "Observed stages").
    const retire = processInconsistency() !== null || processRetirement() !== null;
    if (retire) {
      process.send?.(retiringMessage);
      retainDeclarationSessions(false);
    }
    process.send?.(outcome, () => {
      if (retire) end(0);
    });
  });
  process.on("disconnect", () => end(0));
} else if (process.argv[1] && resolve(process.argv[1]) === import.meta.filename) {
  const all = process.argv.slice(2);
  const budgetAt = all.indexOf("--subtype-rounds");
  const subtypeRounds = budgetAt < 0 ? undefined : Number(all.splice(budgetAt, 2)[1]);
  // `--omit f,g` reads those functions at their declared signatures.
  const omitAt = all.indexOf("--omit");
  const omitted = omitAt < 0 ? [] : (all.splice(omitAt, 2)[1] ?? "").split(",").filter((n) => n !== "");
  const units = { omitted, select: null };
  const typescriptErrors = all.includes("--typescript-errors");
  const args = all.filter((a) => a !== "--typescript-errors");
  if (!(args.length === 1 || (args.length === 3 && args[1] === "--project"))) {
    process.stderr.write("usage: node verify-source.mts file.ts [--project tsconfig-or-directory] [--typescript-errors]" +
      " [--subtype-rounds n] [--omit f,g]\n");
    process.exitCode = 2;
  } else {
    // The printed outcome names the run's directory, kept for inspection.
    keepRunDirectories();
    // The check's collections share a declaration session, released at its end.
    retainDeclarationSessions(true);
    try {
      const result = check(args[0], args[2] ? tsconfigOf(args[2]) : undefined, typescriptErrors, subtypeRounds, false,
        units);
      process.stdout.write(JSON.stringify(result, null, 2) + "\n");
      process.exitCode = result.status === "verified" ? 0 : 1;
    } catch (error) {
      process.stderr.write(messageOf(error) + "\n");
      process.exitCode = 1;
    } finally {
      retainDeclarationSessions(false);
    }
  }
}
