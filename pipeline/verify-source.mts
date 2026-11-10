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
import { decodeSourceClaims, type SourceClaims } from "../tools/source-claims.mts";
// ../tools/source-flow.mts checks the shared execution graph wire before proposal.
import { decodeFlowDocument } from "../tools/source-flow.mts";
import { initOmission } from "../tools/fragment-parse.mts";
import { requireWellFormed, wireText } from "../tools/wire-strings.mts";
import { resolvableDeclaration } from "../tools/intrinsics.mts";
import { assemblyCall } from "./claims-assembly.mts";
import type { AssemblyEntry, Interface, UnitReads } from "./unit-documents.mts";
import { canonicalDocument, decodeUnitFacts, proposalUnits, replaceNumbers, sliceOf, toDocument, type ProposalUnit, type UnitFacts } from "./unit-slices.mts";
import { currentStore, invokeInProcess, invokeProcess, Recorder, readInvocationLog, referenceProposal, reusingEvidence,
  type AttemptRecord } from "./stages.mts";
import { producerBuild, producerCall, producerProtocol, refusalEnd, verifierBuild, verifierCall, verifierProtocol, type ProcessCall, type Protocol } from "./stage-execution.mts";

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

/** A claims document this pipeline's producer wrote, decoded against its
 * TypeScript description; read back by a test that forges it. */
export function readClaimsFile(file: string): SourceClaims {
  const parsed: ParsedJson = JSON.parse(wireText(readFileSync(file), file));
  return decodeSourceClaims(parsed);
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
      /** Under evidence reuse, how many of `units` were checked over reused
       * evidence (STAGE-STORE.md, "Evidence proposals"). */
      reused?: number;
    }
  | {
      status: "unsupported" | "unverified" | "exhausted" | "error";
      artifacts: string;
      detail: string;
      phase: Phase;
      /** A check of each unit's own (`checkUnits`): each unit's result, or
       * null where the file's front refused every unit. */
      units?: UnitResult[] | null;
      reused?: number;
    };
/** A check of each unit: the functions of the file read at their declared
 * signatures (`initOmission` for its initialization), and the units to
 * search and check, by a member's function name (`initOmission` for the
 * initialization), or all. */
export type UnitSelection = { omitted: string[]; select: string[] | null;
  /** Whether each refused unit's result lists the facts its proposal drops
   * (`UnitResult.losses`): one more producer run per refused unit. */
  losses?: boolean };
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
  /** Where the unit's proposal drops facts and why (`producer --explain`),
   * where the check was asked for them (`UnitSelection.losses`). */
  losses?: Explanation[];
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
/** A step run: its exit code, its output, what it reports on failure, and
 * its attempt's record. */
export type StepRun = { code: number; out: string; detail: string; record: AttemptRecord };
/** A process stage run through the common invocation mechanism, its attempt
 * recorded by `recorder`; a search with `reuse` may reuse a proposed entry
 * (`InvokeOptions.reuse`). */
export function runStep(call: ProcessCall, recorder: Recorder | null = null, limitMs: number = stepTimeoutMs,
    reuse: boolean = false): StepRun {
  const p = invokeProcess(call, { limitMs, force: false, recorder, reuse });
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
    record: p.record,
  };
}
export { refusalEnd };
/** A step's refusal record, without its end line, or null where the step
 * succeeded. A refusal is the exit status and the first line's prefix its
 * tool's protocol states (`stage-execution.mts`), and a last line
 * `end of refusal`, so a record cut short is none. Any other exit but 0 (no
 * output, an exception, a usage error, a file it could not read or write,
 * the verifier's 3 and the producer's 3) is a failure of the tool, no
 * verdict. */
function refusalOf(ran: StepRun, step: string, protocol: Protocol): string | null {
  if (ran.code === 0) return null;
  const lines = ran.detail.split("\n");
  const refusal = protocol.refusal;
  if (refusal !== null && ran.code === refusal.status && ran.detail.startsWith(refusal.prefix) && lines.at(-1) === refusalEnd)
    return lines.slice(0, -1).join("\n").trim();
  throw Error(`tool failure: ${step} exited with status ${ran.code} without a complete refusal: ` +
    `${lines[0] || "no output"}`);
}
const verifierRefusal = (ran: StepRun, step: string): string | null => refusalOf(ran, `verifier ${step}`, verifierProtocol);
const producerRefusal = (ran: StepRun): string | null => refusalOf(ran, "the producer", producerProtocol);
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
/** One observation of the producer's (`producer --explain`) at a source
 * span, by `kind`: `form`, a form and why no derivation of it is found;
 * `facts`, a statement or expression past which the proposal states none
 * of `facts`, and what dropped them; `footprint`, an expression that makes
 * the function's inferred footprint `store: any`. */
export interface Explanation {
  kind: "form" | "facts" | "footprint";
  pos: [number, number];
  reason: string;
  facts: string[];
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
 * `{kind, pos, reason, facts}` records, is a tool failure, never "no explanation". */
function readExplanations(ran: StepRun): Explanation[] {
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
    if (!isJsonRecord(e) || Object.keys(e).sort().join() !== "facts,kind,pos,reason") throw malformed("printed a malformed explanation");
    const reason = e["reason"];
    const facts = e["facts"], kind = e["kind"];
    if (!isJsonArray(facts) || !facts.every((f): f is string => typeof f === "string") ||
        (kind !== "form" && kind !== "facts" && kind !== "footprint"))
      throw malformed("printed a malformed explanation");
    const pos = e["pos"];
    const [start, end] = isJsonArray(pos) && pos.length === 2 ? pos : [];
    if (typeof reason !== "string" || typeof start !== "number" || typeof end !== "number")
      throw malformed("printed a malformed explanation");
    return { kind, pos: [start, end], reason, facts: [...facts] };
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
    const meets = explain().filter((e) => e.kind === "form" && e.pos[0] < Math.max(end, start + 1) && start < e.pos[1])
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
 * its unit's claimed footprint and on-throw flag, and the footprint it claims
 * for the function it returns. */
type QualifiedRead = { local: string; declaration: unknown; module: string; name: string;
  footprint: unknown; onThrow: boolean; resultFootprint: unknown };
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
    return [{ local, declaration, module, name, footprint: field(claimed, "footprint"), onThrow,
      resultFootprint: field(claimed, "resultFootprint") }];
  });
}
type FlowDocument = ReturnType<typeof decodeFlowDocument>;
/** A lowering's graphs, or its refusal. */
function lowering(lowered: StepRun): FlowDocument | string {
  return verifierRefusal(lowered, "--lower-control-flow") ?? decodeFlowDocument(JSON.parse(lowered.out));
}
/** A document's proposal, a unit at a time: its claims, or the refusal of
 * the first unit the producer refuses, the initialization's first, then in
 * source order. */
export type Proposed = { claims: string } | { refusal: string };
/** One unit's search: the unit's index and names, its evidence lines at the
 * document's positions, whether they are a reused result, and its search's
 * attempt (none where the search ended at a limit). */
type SearchedUnit = { index: number; names: string[]; ids: string[]; lines: string[]; reused: boolean; record: AttemptRecord | null };
/** The searches of a document's units: each unit's, each refused unit's
 * refusal, and each search that ended at a limit, by its members' names. */
type Searched = { units: SearchedUnit[]; refused: Map<string, string>; failed: Map<string, string> };
/** The evidence lines of every unit searched, in order. */
const evidenceLines = (searched: Searched): string[] => searched.units.flatMap((u) => u.lines);
/** `searched` with the units `again` searched again in their place. */
function searchedAgain(searched: Searched, again: Searched): Searched {
  const refused = new Map(searched.refused), failed = new Map(searched.failed);
  for (const u of again.units) for (const n of u.names) {
    refused.delete(n);
    failed.delete(n);
  }
  for (const [n, r] of again.refused) refused.set(n, r);
  for (const [n, r] of again.failed) failed.set(n, r);
  return { units: searched.units.map((u) => again.units.find((a) => a.index === u.index) ?? u), refused, failed };
}
/** A document proposed unit by unit (`unit-slices.mts`): the producer's
 * units of the document (`producer --units`), each unit's slice lowered and
 * proposed (`producer --unit`) after the units it reads, at their settled
 * footprints and flags, and the units' proposals assembled into the
 * document's claims (`producer --assemble`). */
export class UnitProposal {
  private readonly run: (call: ProcessCall, reuse?: boolean) => StepRun;
  private readonly prefix: string;
  private readonly document: JsonObject;
  private readonly local: string;
  private readonly units: ProposalUnit[];
  private readonly facts: UnitFacts;
  private readonly slices = new Map<number, { slice: string; flow: string; deletions: [number, number][]; symbols: number[] }>();
  private settled = new Map<string, Interface>();
  /** The qualified reads of the last proposal. */
  private proposedAt: QualifiedRead[] = [];
  /** Each proposed unit's slice and claims, what its search reads. */
  private searchable = new Map<number, { slice: string; claims: string; qualified: string; deletions: [number, number][]; symbols: number[] }>();
  private qualified = "";
  private readonly refusal: string | null;
  /** `flow` is the document's lowering where the caller holds it. */
  constructor(run: (call: ProcessCall, reuse?: boolean) => StepRun, prefix: string, ast: string, local: string,
      flow?: FlowDocument) {
    this.run = run;
    this.prefix = prefix;
    this.local = local;
    const parsed: unknown = JSON.parse(readFileSync(ast, "utf8"));
    if (!isObject(parsed)) throw Error("tool failure: a document is no object");
    this.document = parsed;
    const listed = run(producerCall(producerExecutable, ["--units", ast]));
    // A document the producer refuses to read is refused by each proposal.
    this.refusal = producerRefusal(listed);
    this.facts = this.refusal !== null ? { functions: [], init: null, escaped: [], readAsValues: [] } : decodeUnitFacts(JSON.parse(listed.out));
    if (this.refusal === null) {
      const graphs = flow ?? lowering(run(verifierCall(verifier, ["--lower-control-flow", ast])));
      if (typeof graphs === "string") this.refusal = graphs;
      else {
        for (const f of this.facts.functions) {
          for (const member of list(this.document.functions)) {
            if (field(member, "name") !== f.name) continue;
            const pos = spanOf(field(member, "namePos"));
            const graph = graphs.find((g) => pos && g.owner[0] === pos[0] && g.owner[1] === pos[1]);
            if (!graph) throw Error(`tool failure: no lowering reads for ${f.name}`);
            f.names = [...new Set([...f.names, ...graph.moduleReads])].sort();
          }
        }
        if (this.facts.init) {
          const graph = graphs.find((g) => g.owner[0] === 0 && g.owner[1] === 0);
          if (!graph) throw Error("tool failure: no initialization lowering reads");
          this.facts.init.names = [...new Set([...this.facts.init.names, ...graph.moduleReads])].sort();
        }
      }
    }
    this.units = proposalUnits(this.facts);
  }
  /** The slice of unit `i`, lowered: its files, or the lowering's refusal. */
  private slice(i: number): { slice: string; flow: string; deletions: [number, number][]; symbols: number[] } | string {
    const held = this.slices.get(i);
    if (held) return held;
    const unit = this.units[i];
    if (!unit) throw Error(`tool failure: no unit ${i}`);
    const { text, deletions, symbols } = sliceOf(this.document, this.local, unit, this.facts.escaped);
    const slice = `${this.prefix}unit-${i}.slice.json`, flow = `${this.prefix}unit-${i}.flow.json`;
    writeFileSync(slice, text);
    const lowered = this.run(verifierCall(verifier, ["--lower-control-flow", slice]));
    const refusal = verifierRefusal(lowered, "--lower-control-flow");
    if (refusal !== null) return refusal;
    writeFileSync(flow, JSON.stringify(decodeFlowDocument(JSON.parse(lowered.out))));
    const files = { slice, flow, deletions, symbols };
    this.slices.set(i, files);
    return files;
  }
  private reads(unit: ProposalUnit, interfaces: Map<string, Interface>, qualified: QualifiedRead[]): string {
    const pinned = unit.reads.map((name): Interface => {
      const settled = interfaces.get(name);
      if (!settled) throw Error(`tool failure: unit read ${name} before its proposal`);
      return settled;
    });
    // The constants read as values are read by the initialization alone, and
    // a qualified read by the code that names it: a unit's slice holds each
    // only where they are among its inputs.
    const document: UnitReads = { members: unit.members, init: unit.init, pinned,
      readAsValues: unit.holdsInit ? this.facts.readAsValues : [],
      qualified: qualified.filter((q) => unit.names.includes(q.local))
        .map(({ local, declaration, footprint, onThrow, resultFootprint }) =>
          ({ local, declaration, footprint, onThrow, resultFootprint })) };
    return JSON.stringify(document);
  }
  /** The document's claims at the qualified reads `qualified`. */
  propose(qualified: QualifiedRead[]): Proposed {
    if (this.refusal !== null) return { refusal: this.refusal };
    const interfaces = new Map<string, Interface>();
    const refused: { order: number; refusal: string }[] = [];
    const proposals: { bin: string; deletions: [number, number][]; symbols: number[] }[] = [];
    const order = (unit: ProposalUnit): number => unit.init ? -1
      : Math.min(...unit.members.map((m) => this.facts.functions.findIndex((f) => f.name === m)));
    for (const [i, unit] of this.units.entries()) {
      if (!unit.reads.every((n) => interfaces.has(n))) continue;
      const files = this.slice(i);
      if (typeof files === "string") {
        refused.push({ order: order(unit), refusal: files });
        continue;
      }
      const reads = `${this.prefix}unit-${i}.reads.json`, bin = `${this.prefix}unit-${i}.proposal.bin`,
        claims = `${this.prefix}unit-${i}.claims.json`;
      writeFileSync(reads, this.reads(unit, interfaces, qualified));
      const proposed = this.run(producerCall(producerExecutable, ["--unit", files.slice, files.flow, reads, bin, claims]));
      const refusal = producerRefusal(proposed);
      if (refusal !== null) {
        // A refusal's spans, at the document's positions.
        refused.push({ order: order(unit), refusal: replaceNumbers(refusal, /\[(\d+),(\d+)\)/g, (y) => toDocument(files.deletions, y)) });
        continue;
      }
      for (const entry of decodeInterfaces(JSON.parse(proposed.out))) interfaces.set(entry.name, entry);
      proposals.push({ bin, deletions: files.deletions, symbols: files.symbols });
      const searchQualified = `${this.prefix}unit-${i}.search-qualified.json`;
      writeFileSync(searchQualified, JSON.stringify(qualified.filter((q) => unit.names.includes(q.local))
        .map(({ local, footprint, onThrow, resultFootprint }) => ({ name: local, footprint, onThrow, resultFootprint }))));
      this.searchable.set(i, { slice: files.slice, claims, qualified: searchQualified, deletions: files.deletions, symbols: files.symbols });
    }
    this.settled = interfaces;
    this.proposedAt = qualified;
    this.qualified = `${this.prefix}search-qualified.json`;
    writeFileSync(this.qualified, JSON.stringify(qualified.map(({ local, footprint, onThrow, resultFootprint }) =>
      ({ name: local, footprint, onThrow, resultFootprint }))));
    const first = refused.sort((a, b) => a.order - b.order)[0];
    if (first) return { refusal: first.refusal };
    const canonical = `${this.prefix}canonical.json`, assembly = `${this.prefix}assembly.json`,
      qualifiedPath = `${this.prefix}qualified.json`;
    writeFileSync(canonical, canonicalDocument(this.document, this.local));
    writeFileSync(assembly, JSON.stringify(proposals.map((p): AssemblyEntry => ({ deletions: p.deletions, symbols: p.symbols }))));
    writeFileSync(qualifiedPath, JSON.stringify(qualified.map(({ local, declaration, footprint, onThrow, resultFootprint }) =>
      ({ local, declaration, footprint, onThrow, resultFootprint }))));
    const assembled = this.run(producerCall(producerExecutable,
      ["--assemble", canonical, qualifiedPath, assembly, ...proposals.map((p) => p.bin)]));
    const refusal = producerRefusal(assembled);
    if (refusal !== null) throw Error(`tool failure: the producer's assembly refused: ${refusal}`);
    return { claims: assembled.out.trim() };
  }
  /** Each unit's search over its slice (`verifier --produce-unit`), the
   * units `select` names or all, after `propose`: the evidence lines, each
   * unit named and its spans placed at the document's positions, for the
   * check to write over the document's store; each refused unit's refusal,
   * and each search that ended at a limit, by its members' names. With
   * `reuse`, a search may reuse evidence another implementation found
   * (STAGE-STORE.md, "Evidence proposals"): a reused result is used only
   * where it is a complete success whose every line names its unit and
   * relocates to the document's symbols; any other is a miss, and the unit
   * is searched with reuse off. */
  search(budget: string[], select: string[] | null, reuse: boolean = false): Searched {
    const units: SearchedUnit[] = [], refused = new Map<string, string>(), failed = new Map<string, string>();
    for (const [i, files] of this.searchable) {
      const unit = this.units[i];
      if (!unit) throw Error(`tool failure: no unit ${i}`);
      const names = [...unit.members, ...(unit.init ? [initOmission] : [])];
      const ids = list(this.document.functions).flatMap((f) => {
        const name = field(f, "name"), pos = spanOf(field(f, "namePos"));
        return typeof name === "string" && unit.members.includes(name) && pos ? [`${name}@${pos[0]}`] : [];
      });
      if (unit.init) ids.push("init");
      if (select !== null && !names.some((n) => select.includes(n))) continue;
      // A refusal's spans, at the document's positions: `[a,b)` in its
      // text, and its diagnostics' positions, spans and obligation ids.
      const at = (detail: string): string => [/\[(\d+),(\d+)\)/g, /"(?:pos|span|subject|namePos)":\[(\d+),(\d+)\]/g,
        /"id":"[a-z-]+:(\d+)[:"]/g].reduce((text, pattern) =>
        replaceNumbers(text, pattern, (y) => toDocument(files.deletions, y)), detail);
      const named = (id: string): string => {
        const at = /@(\d+)$/.exec(id);
        return at?.[1] === undefined ? id : `${id.slice(0, at.index)}@${toDocument(files.deletions, Number(at[1]))}`;
      };
      const evidence = `${this.prefix}unit-${i}.evidence.json`;
      const call = verifierCall(verifier, [...budget, "--produce-unit", files.slice, files.claims, files.qualified,
        evidence, String(searchDepth), names.join(",")]);
      // The search, its evidence file written afresh, or the limit it ended at.
      const searchedWith = (reusing: boolean): StepRun | { limit: string } => {
        rmSync(evidence, { force: true });
        try {
          return this.run(call, reusing);
        } catch (error) {
          if (!overLimit(messageOf(error))) throw error;
          return { limit: messageOf(error) };
        }
      };
      // The evidence lines the search wrote, each unit named and relocated.
      const written = (): string[] => readFileSync(evidence, "utf8").split("\n").filter((l) => l !== "").map((line) => {
        // A line's fields are in key order, its unit last: spliced as text,
        // the evidence passes through unread.
        const unitAt = /"unit":("(?:[^"\\]|\\.)*")\}$/.exec(line);
        const id: unknown = unitAt?.[1] === undefined ? undefined : JSON.parse(unitAt[1]);
        if (unitAt === null || typeof id !== "string")
          throw Error("tool failure: verifier --produce-unit wrote a line without its unit");
        const relocated = replaceNumbers(line.slice(0, unitAt.index), /"symbolLit":\{"id":(\d+)\}|"symbol":(\d+)/g, (i) => {
          const symbol = files.symbols[i];
          if (symbol === undefined) throw Error("tool failure: evidence names an absent slice symbol");
          return symbol;
        });
        return `${relocated}"unit":${JSON.stringify(named(id))}}`;
      });
      let produced = searchedWith(reuse);
      if (!("limit" in produced) && produced.record.execution === "reused") {
        let lines: string[] | null = null;
        try {
          if (produced.code === 0 && !produced.out.split("\n").some((l) => l.startsWith("refused: "))) lines = written();
        } catch {
          lines = null;
        }
        if (lines !== null && lines.length === 1) {
          units.push({ index: i, names, ids, lines, reused: true, record: produced.record });
          continue;
        }
        produced = searchedWith(false);
      }
      if ("limit" in produced) {
        for (const n of names) failed.set(n, produced.limit);
        units.push({ index: i, names, ids, lines: [], reused: false, record: null });
        continue;
      }
      const refusal = verifierRefusal(produced, "--produce-unit");
      const out = produced.out.split("\n");
      if (refusal !== null && !out.some((l) => l.startsWith("checked source evidence written: "))) {
        for (const n of names) refused.set(n, at(refusal));
        units.push({ index: i, names, ids, lines: [], reused: false, record: produced.record });
        continue;
      }
      for (const l of out.filter((l) => l.startsWith("refused: "))) {
        const value: unknown = JSON.parse(l.slice("refused: ".length));
        const id = field(value, "unit"), detail = field(value, "refusal");
        if (typeof id !== "string" || typeof detail !== "string")
          throw Error("tool failure: verifier --produce-unit printed a malformed refusal");
        refused.set(memberName(named(id)), at(detail));
      }
      units.push({ index: i, names, ids, lines: written(), reused: false, record: produced.record });
    }
    return { units, refused, failed };
  }
  /** The explanations of the unit holding the member `member` (a function's
   * name, or `init`), at the document's positions. */
  explain(member: string): Explanation[] {
    const i = this.units.findIndex((u) => member === "init" ? u.init : u.members.includes(memberName(member)));
    const unit = this.units[i];
    if (!unit) return [];
    const files = this.slice(i);
    if (typeof files === "string") return [];
    const reads = `${this.prefix}unit-${i}.explain.json`;
    // An explanation reads its neighbours at their settled footprints and
    // flags, and its imports as the last proposal read them.
    writeFileSync(reads, this.reads(unit, this.settled, this.proposedAt));
    return readExplanations(this.run(producerCall(producerExecutable, ["--explain", files.slice, files.flow, reads]))).map((e) => ({ ...e, pos: [toDocument(files.deletions, e.pos[0]), toDocument(files.deletions, e.pos[1])] }));
  }
}
function decodeInterfaces(value: unknown): Interface[] {
  if (!Array.isArray(value)) throw Error("tool failure: producer --unit printed no interfaces");
  return value.map((v): Interface => {
    const name = field(v, "name"), thrown = field(v, "thrown"), footprint = field(v, "footprint"),
      resultFootprint = field(v, "resultFootprint");
    if (typeof name !== "string" || typeof thrown !== "boolean" || footprint === undefined || resultFootprint === undefined)
      throw Error("tool failure: producer --unit printed a malformed interface");
    return { name, footprint, thrown, resultFootprint };
  });
}
type JsonObject = { [key: string]: import("../tools/calculus.mts").Json };
const isObject = (value: unknown): value is JsonObject =>
  typeof value === "object" && value !== null && !Array.isArray(value);
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
    imports: string[]; proposal: UnitProposal }>();
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
        init: field(m, "init"), functions: field(m, "functions"), modules: [], omittedMentions: [] };
      const ast = join(artifacts, `module-${index}.fragment.json`);
      writeFileSync(ast, JSON.stringify(doc));
      const lowered = runStep(verifierCall(verifier, ["--lower-control-flow", ast]), recorder);
      // A module the verifier refuses to lower is read at its declared types.
      if (verifierRefusal(lowered, "--lower-control-flow") !== null) continue;
      const flow = join(artifacts, `module-${index}.flow.json`), graphs = decodeFlowDocument(JSON.parse(lowered.out));
      writeFileSync(flow, JSON.stringify(graphs));
      const imports = [...new Set(list(field(doc.declarations, "values")).map((v) => field(field(v, "declaration"), "module"))
        .filter((l): l is string => typeof l === "string" && l !== location && locations.includes(l)))];
      this.docs.set(location, { index, ast, flow, declarations: doc.declarations, imports,
        proposal: new UnitProposal((call, reuse) => runStep(call.stage === "search" ? { ...call, stage: "module-search" } : call,
          recorder, stepTimeoutMs, reuse), join(artifacts, `module-${index}.`), ast, location, graphs) });
      this.units.set(location, list(field(m, "functions")));
    }
  }
  /** Search the selected module units through their proposals' slices. */
  search(location: string, names: string[], budget: string[], reuse: boolean): Searched {
    const doc = this.docs.get(location);
    if (!doc) throw Error(`tool failure: no proposal for module ${location}`);
    return doc.proposal.search(budget, names, reuse);
  }
  /** The name of the function of `module` whose source holds the first span
   * `detail` names (`at [a,b)`), from its name to its body's last statement;
   * null where none does. */
  functionAt(module: string, detail: string): string | null {
    const at = /at \[(\d+),(\d+)\)/.exec(detail);
    if (!at?.[1] || !at[2]) return null;
    const start = Number(at[1]), end = Number(at[2]);
    for (const f of this.units.get(module) ?? []) {
      const name = field(f, "name"), from = spanOf(field(f, "namePos"));
      const last = list(field(f, "body")).reduce((n: number, st) => Math.max(n, spanOf(field(st, "pos"))?.[1] ?? n), -1);
      if (typeof name === "string" && from && from[0] <= start && end <= last) return name;
    }
    return null;
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
        const proposed = doc.proposal.propose(reads);
        writeFileSync(join(this.artifacts, `module-${doc.index}.proposal.log`), "refusal" in proposed ? proposed.refusal : "");
        // A module the producer refuses is read at its declared types.
        this.proposed.set(key, "refusal" in proposed ? null : { text: proposed.claims, parsed: JSON.parse(proposed.claims) });
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

/** One round of a check of each unit: each module run the file's claims plan
(`--module-runs`), searched and checked on its own over its restricted
document (`--check-module`), its search through the same unit slices, then the search of each of
the file's selected units over its own slice (`UnitProposal.search`), and
their check over the file's one front (`--check-units`), which writes each
slice's evidence over the document's store. A unit's search over its limit
is that unit's outcome. A refusal naming a certified import asks for that
import's withdrawal, every such import of the round at once, before the
check; a refused front refuses every unit. Under evidence reuse
(STAGE-STORE.md, "Evidence proposals"), each fallback to a search with
reuse off completes before the round's withdrawal decision: a module run
whose check refuses or fails while any of its lines is reused is searched
again with reuse off and checked once more; the file's units whose lines
are reused and refused are searched again and checked once more, and a
later refusal of a reused unit, or a check with a reused line that fails
as a whole, searches every unit still reused for a last check: at most two
checks per module run and three for the file. `reused` counts the units
checked over reused evidence, a module run as one. */
function unitRound(recorder: Recorder, artifacts: string, ast: string, claims: string, snapshot: string,
    budget: string[], select: string[] | null, proposal: UnitProposal, modules: ModuleRuns,
    refusedRead: (module: string, detail: string) => string | null):
    { withdraw: string[] } | { front: string } | { results: UnitResult[]; reused: number } {
  const reuse = reusingEvidence();
  const named = select === null ? [] : [select.join(",")];
  const strings = (value: unknown): string[] => {
    if (!Array.isArray(value) || !value.every((x): x is string => typeof x === "string"))
      throw Error("tool failure: verifier listed a unit without its members or dependencies");
    return value;
  };
  const check = (evidence: string, names: string[], refused: Map<string, string>, failed: Map<string, string>):
      UnitResult[] | string => {
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
      const limit = failed.get(memberName(unit));
      if (limit !== undefined) return { unit, members, status: "error", phase: "search", detail: limit, depends: [] };
      const searchRefusal = refused.get(memberName(unit));
      const reason = searchRefusal ?? field(value, "refusal");
      if (typeof reason !== "string") throw Error("tool failure: verifier --check-units printed a verdict without its refusal");
      // A unit's refusal reads as the verifier's refusal of a command does.
      const detail = `reject: ${reason}`;
      return { unit, members, status: refusalStatus(detail), phase: searchRefusal !== undefined ? "search" : "check",
        detail, depends: [] };
    });
  };
  // The certified imports refusals name, each once: a module run's refusal
  // within a function the round reads, that read alone (`refusedRead`).
  const withdrawal = (details: Iterable<string>): { withdraw: string[] } | null => {
    const keys = new Set<string>();
    for (const detail of details) {
      const failed = failedImport(detail);
      if (failed) keys.add(`${failed.module}#${failed.name ?? refusedRead(failed.module, detail) ?? "*"}`);
    }
    return keys.size ? { withdraw: [...keys] } : null;
  };
  // One verdict per searched group, naming exactly its members. Coverage
  // includes searched units as well as reused ones.
  const verdictsOf = (u: SearchedUnit, results: readonly UnitResult[]): UnitResult[] =>
    results.filter((r) => u.names.includes(memberName(r.unit)));
  const completeVerdict = (u: SearchedUnit, results: readonly UnitResult[]): boolean => {
    const matches = verdictsOf(u, results);
    const r = matches[0];
    return matches.length === 1 && r !== undefined && u.ids.includes(r.unit) &&
      r.members.length === u.ids.length && new Set(r.members).size === u.ids.length &&
      u.ids.every((id) => r.members.includes(id));
  };
  const accepted = (u: SearchedUnit, results: readonly UnitResult[]): boolean =>
    completeVerdict(u, results) && verdictsOf(u, results).every((r) => r.status === "verified");
  let reused = 0;
  // The module runs, each keyed on its restricted document: an importer's
  // edit that keeps a closure replays its search and check.
  const planned = runStep(verifierCall(verifier, [...budget, "--module-runs", ast, claims]), recorder);
  const planRefusal = verifierRefusal(planned, "--module-runs");
  if (planRefusal !== null) return withdrawal([planRefusal]) ?? { front: planRefusal };
  const moduleResults: UnitResult[] = [];
  const moduleSearchRefusals: string[] = [];
  for (const [index, line] of planned.out.split("\n").filter((l) => l.startsWith("{")).entries()) {
    const run = join(artifacts, `module-run-${index}.json`), own = join(artifacts, `module-run-${index}.evidence.json`);
    writeFileSync(run, line);
    const plannedRun: unknown = JSON.parse(line);
    const location = field(plannedRun, "location");
    if (typeof location !== "string") throw Error("tool failure: a module run has no location");
    const names = list(field(field(plannedRun, "ast"), "functions")).map((f) => {
      const name = field(f, "name");
      if (typeof name !== "string") throw Error("tool failure: a module function has no name");
      return name;
    });
    const checkModule = (lines: readonly string[]): unknown => {
      writeFileSync(own, `[${lines.join(",")}]`);
      const checked = runStep(verifierCall(verifier, [...budget, "--check-module", run, own]), recorder);
      const verdicts = checked.out.split("\n").filter((l) => l.startsWith("{"));
      const verdict = verdicts[0];
      const refusal = verifierRefusal(checked, "--check-module");
      if (verdict === undefined) throw Error(`tool failure: verifier --check-module printed no verdict: ${refusal ?? ""}`);
      const value: unknown = JSON.parse(verdict);
      if (verdicts.length !== 1 || field(value, "unit") !== `module:${location}`)
        throw Error("tool failure: verifier --check-module printed unexpected verdicts");
      return value;
    };
    let searched = modules.search(location, [...names, initOmission], budget, reuse);
    let value: unknown = null;
    for (;;) {
      const refused = [...searched.refused.values(), ...searched.failed.values()];
      if (refused.length) {
        moduleSearchRefusals.push(...refused.map((reason) => `module ${location}: ${reason}`));
        break;
      }
      const again = searched.units.filter((u) => u.reused);
      if (again.length === 0) {
        value = checkModule(evidenceLines(searched));
        break;
      }
      try {
        value = checkModule(evidenceLines(searched));
      } catch {
        value = null;
      }
      if (field(value, "accepted") === true) break;
      searched = searchedAgain(searched, modules.search(location, again.flatMap((u) => u.names), budget, false));
    }
    if (searched.refused.size > 0 || searched.failed.size > 0) continue;
    const unit = field(value, "unit"), reason = field(value, "refusal");
    if (typeof unit !== "string") throw Error("tool failure: verifier --check-module printed a verdict without its unit");
    if (field(value, "accepted") === true) {
      moduleResults.push({ unit, members: [], status: "verified", phase: "check", detail: "", depends: [] });
      if (searched.units.some((u) => u.reused)) reused++;
      for (const u of searched.units) if (!u.reused && u.record !== null) referenceProposal(u.record);
    } else if (typeof reason === "string") {
      const detail = `reject: ${reason}`;
      moduleResults.push({ unit, members: [], status: refusalStatus(detail), phase: "check", detail, depends: [] });
    } else throw Error("tool failure: verifier --check-module printed a verdict without its refusal");
  }
  const moduleWithdrawn = withdrawal([...moduleSearchRefusals,
    ...moduleResults.filter((r) => r.status !== "verified").map((r) => r.detail)]);
  if (moduleWithdrawn) return moduleWithdrawn;
  let searched = proposal.search(budget, select, reuse);
  const withdrawn = withdrawal(searched.refused.values());
  if (withdrawn) return withdrawn;
  const evidence = join(artifacts, "evidence.json");
  let checked: UnitResult[] | string;
  for (let attempt = 0; ; attempt++) {
    writeFileSync(evidence, evidenceLines(searched).map((l) => l + "\n").join(""));
    const reusedUnits = searched.units.filter((u) => u.reused);
    if (reusedUnits.length === 0) {
      checked = check(evidence, named, searched.refused, searched.failed);
      break;
    }
    let outcome: UnitResult[] | null;
    try {
      const c = check(evidence, named, searched.refused, searched.failed);
      outcome = typeof c === "string" ? null : c;
    } catch {
      outcome = null;
    }
    const results = outcome !== null && searched.units.every((u) => completeVerdict(u, outcome)) &&
      outcome.length === searched.units.length ? outcome : null;
    const refusedReused = results === null ? reusedUnits
      : reusedUnits.filter((u) => !accepted(u, results));
    if (results !== null && refusedReused.length === 0) {
      checked = results;
      break;
    }
    const again = results === null || attempt > 0 ? reusedUnits : refusedReused;
    searched = searchedAgain(searched, proposal.search(budget, again.flatMap((u) => u.names), false));
  }
  if (typeof checked === "string") return withdrawal([checked]) ?? { front: checked };
  let results = checked;
  for (const u of searched.units) {
    if (!accepted(u, results)) continue;
    if (u.reused) reused++;
    else if (u.record !== null) referenceProposal(u.record);
  }
  // In the front's order, the file's functions by position, then its
  // initialization: the order the units' searches end in is the slices'.
  const place = (unit: string): number => unit === "init" ? Infinity : Number(/@(\d+)$/.exec(unit)?.[1] ?? Infinity);
  results = [...results].sort((a, b) => place(a.unit) - place(b.unit));
  return withdrawal(results.filter((r) => r.status !== "verified").map((r) => r.detail)) ??
    { results: [...results, ...moduleResults], reused };
}

/** Whether a unit's search ended at a limit: its time limit, or its memory
 * limit, at which the runner stopped it (`stage-execution.mts`). */
function overLimit(message: string): boolean {
  return message.startsWith("timeout: ") || /^tool failure: [^:]* --produce-unit\b[^:]*: memory limit: /.test(message);
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
    const graphs = decodeFlowDocument(JSON.parse(lowered.out));
    writeFileSync(flow, JSON.stringify(graphs));
    phase = "proposal";
    // Certified imports: each module's claims, and the reads they may
    // qualify. A read the search or the check refuses, or a module run it
    // refuses, is withdrawn, and the documents proposed again without it.
    // Each module run is searched and checked in stages of its own, keyed on
    // its restricted document (`unitRound`), so a later round, and a later
    // edit of the importer, replays the runs it leaves unchanged.
    const modules = new ModuleRuns(recorder, artifacts, parsedData);
    const fileProposal = new UnitProposal((call, reuse) => runStep(call, recorder, stepTimeoutMs, reuse), `${artifacts}/`, ast,
      resolution, graphs);
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
      const proposed = fileProposal.propose(reads);
      writeFileSync(join(artifacts, "proposal.log"), "refusal" in proposed ? proposed.refusal : "");
      if ("refusal" in proposed)
        return { status: "unsupported", artifacts, phase, detail: refusedByTypeScript(proposed.refusal, refusedErrors) };
      // The importer's claims, its `modules` the claims `used`.
      const assembled = invokeInProcess(assemblyCall(proposed.claims, used), { force: false, recorder }).value;
      writeFileSync(claims, assembled);
      // The document has the shape its TypeScript description states, its
      // modules' included; a field the producer writes otherwise fails the run.
      const document: ParsedJson = JSON.parse(assembled);
      decodeSourceClaims(document);
      phase = "search";
      // A module run's refusal at a span within a function of the module
      // that a document of the round reads: that read, which the run's
      // check reached; the module's other reads are kept.
      const readNames = new Set([...reads, ...[...readsOf.values()].flat()].map((r) => `${r.module}#${r.name}`));
      const refusedRead = (module: string, detail: string): string | null => {
        const name = modules.functionAt(module, detail);
        return name !== null && readNames.has(`${module}#${name}`) ? name : null;
      };
      const round = unitRound(recorder, artifacts, ast, claims, snapshot, budget, units.select, fileProposal, modules, refusedRead);
      if ("withdraw" in round) {
        const again = round.withdraw.find((w) => withdrawn.has(w));
        if (again !== undefined) return { status: "error", artifacts, phase,
          detail: `a refusal names the certified import ${again} again after its withdrawal`, units: null };
        for (const w of round.withdraw) withdrawn.add(w);
        continue;
      }
      if ("front" in round)
        return { status: refusalStatus(round.front), artifacts, phase, detail: round.front, units: null };
      if (units.losses) for (const u of round.results)
        if (u.members[0] !== undefined && (units.select === null || u.members.some((m) => units.select?.includes(memberName(m)))))
          u.losses = fileProposal.explain(u.members[0]).filter((e) => e.kind !== "form");
      const first = round.results.find((u) => u.status !== "verified");
      const reused = reusingEvidence() ? { reused: round.reused } : {};
      if (first === undefined)
        return { status: "verified", artifacts, phase: "check", functions, initialization, units: round.results, ...reused };
      // The file's refusal is its first unit's, a search's named as a whole-file search names it.
      const detail = first.phase === "search" && first.status !== "error"
        ? refusedByName(namingTheObligation(first.detail, bytes.toString("utf8")),
          () => fileProposal.explain(first.members[0] ?? ""),
          refusedErrors)
        : first.detail;
      return { status: first.status === "verified" ? "error" : first.status, artifacts, phase: first.phase,
        detail, units: round.results, ...reused };
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
  const given = "reused" in value ? value.reused : undefined;
  if (given !== undefined && (typeof given !== "number" || !Number.isSafeInteger(given) || given < 0))
    throw Error("not an outcome: its reused count is no natural number");
  const reused = given === undefined ? {} : { reused: given };
  if (status === "verified" && phase === "check" && "functions" in value && Array.isArray(value.functions) &&
      value.functions.every((f: unknown) => typeof f === "string") && "initialization" in value &&
      Array.isArray(value.initialization) && value.initialization.every(isSpan))
    return { status, artifacts, phase, functions: value.functions, initialization: value.initialization,
      ...(units === undefined ? {} : { units: readUnitResults(units) }), ...reused };
  if ((status === "unsupported" || status === "unverified" || status === "exhausted" || status === "error") &&
      "detail" in value && typeof value.detail === "string")
    return { status, artifacts, phase, detail: value.detail,
      ...(units === undefined ? {} : { units: units === null ? null : readUnitResults(units) }), ...reused };
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
    const given = field(u, "losses");
    if (given === undefined) return { unit, members, status, phase, detail, depends };
    if (!Array.isArray(given)) throw Error("not an outcome: a unit result is malformed");
    const losses = given.map((e: unknown): Explanation => {
      const pos = field(e, "pos"), reason = field(e, "reason"), facts = strings(field(e, "facts")), kind = field(e, "kind");
      const [start, end] = Array.isArray(pos) && pos.length === 2 ? pos : [];
      if (typeof start !== "number" || typeof end !== "number" || typeof reason !== "string" || !facts ||
          (kind !== "facts" && kind !== "footprint"))
        throw Error("not an outcome: a unit result is malformed");
      return { kind, pos: [start, end], reason, facts };
    });
    return { unit, members, status, phase, detail, depends, losses };
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
  const units: UnitSelection = { omitted, select: select === null ? null : strings(select),
    losses: field(given, "losses") === true };
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
