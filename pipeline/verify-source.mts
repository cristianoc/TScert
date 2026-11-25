import { fork, type ChildProcess } from "node:child_process";
import { readFileSync, writeFileSync, rmSync } from "node:fs";
import { Socket } from "node:net";
import { availableParallelism } from "node:os";
import { basename, resolve, join } from "node:path";
import { createHash } from "node:crypto";
// ../tools/fragment-parse.mts is the trusted parser and syntactic gate: without it no source becomes the Fragment Lean reads.
import { close as closeParser } from "../tools/fragment-parse.mts";
import { diagnosticsCall, parseCall, type Parsed } from "./parse-stage.mts";
import { processInconsistency, processRetirement } from "../tools/files.mts";
import { retainDeclarationSessions } from "../tools/declaration-session.mts";
import { tsconfigOf, type SeenDiagnostic } from "../tools/declaration-graph.mts";
import { readDiagnostic } from "../tools/diagnostic.mts";
import { presentObligation } from "../tools/diagnostic-view.mts";
import { fieldOf, messageOf } from "../tools/thrown.mts";
import { keepRunDirectories, ownedRun, requireDiskSpace, runDirectory, runRoot, withinRunDirectory } from "./run-directory.mts";
import type { Json as ParsedJson } from "../tools/calculus.mts";
import type { Ast } from "../tools/fragment.mts";
import type { BodyFact, BodyVariable, CallEffect, DeclarationDocument, DeclarationIdentity, IndexFact as StatedFact, Integer,
  LinearTerm, PropertyKey, Region, Selector, TypeDefinition, TypeTerm } from "../tools/declaration-types.mts";
import type { BodyFormula, BodyVariable as FactVariable, IndexFact, LinearTerm as FactTerm } from "../tools/diagnostic.mts";
import { indexFact } from "../tools/fact-text.mts";
import { initOmission } from "../tools/fragment-parse.mts";
import { requireWellFormed, wireText } from "../tools/wire-strings.mts";
import { intrinsicModule, resolvableDeclaration } from "../tools/intrinsics.mts";
import { interfaceOverlay, primitiveKinds } from "../tools/array-prototype.mts";
import { hostPackage } from "../tools/compiler-api.mts";
import { globalOrigins, globalsOverlay } from "../tools/library-globals.mts";
import { moduleEntries } from "../tools/library-modules.mts";
import { libraryRegExpNames } from "../tools/regexp.mts";
import { currentStore, invokeInProcess, invokeProcess, Recorder, readInvocationLog, type AttemptRecord } from "./stages.mts";
import { verifyByUnits } from "./module-interfaces.mts";
import type { CheckedUnits } from "./module-interfaces.mts";
import { decodeContractRead, decodeVerdictLine, decodeWorkerPrepared, type ContractRead } from "./stage-execution.mts";
import type { WorkerPart } from "./stages.mts";
import { refusalEnd, verifier, verifierProtocol, type ProcessCall, type Protocol } from "./stage-execution.mts";

/** The file of a run's directory holding its stage invocations' attempts. */
export const invocationLog = "invocations.jsonl";

/** A Fragment document this pipeline's parser wrote, read back by a test that
 * forges it, or by `--contracts`, which renders the declarations the check
 * read from it. The tests (18 reads) edit fields deep in the document through
 * its type; checking those fields at each test, in place of this assertion,
 * would rewrite each of them, and no TypeScript decoder of the Fragment
 * exists. The assertion stands for the parser's output; it is not checked
 * before a reader reads it. */
export function readFragmentFile(file: string): Ast {
  const parsed: ParsedJson = JSON.parse(wireText(readFileSync(file), file));
  requireWellFormed(parsed, file);
  const fragment: unknown = parsed;
  return fragment as Ast; // asserted: the parser wrote the file from an Ast; a check of every field the tests read would cost more than it guards a test's forgery
}

/** The file identity a run's Fragment names, its snapshot's path: what the
 * pass takes as the file key. */
export function sourceKey(artifacts: string): string {
  return readFragmentFile(join(artifacts, "fragment.json")).file;
}

const here = import.meta.dirname;
const repo = resolve(here, "..");
export { verifier };
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
      contractReads?: UnitContracts[];
    }
  | {
      status: "unsupported" | "unverified" | "exhausted" | "error";
      artifacts: string;
      detail: string;
      phase: Phase;
      /** A check of each unit's own (`checkUnits`): each unit's result, or
       * null where the file's front refused every unit. */
      units?: UnitResult[] | null;
      contractReads?: UnitContracts[];
    };
/** The contracts a unit's check read, as its verdict line records them
 * (`VerdictLine`'s `contracts`): reported beside the verdict, read by none. */
export type UnitContracts = { unit: string; reads: ContractRead[] };
/** A check of each unit: the functions of the file read at their declared
 * signatures (`initOmission` for its initialization), and the units the
 * caller reads, by a member's function name (`initOmission` for the
 * initialization), or all: a selection lifts the check's overall time
 * limit, each stage keeping its own. */
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
/** Wall-clock limit on each external step (the interface stages, the
 * pass, the lowering): `TSCERT_STEP_LIMIT` seconds, 60 by default. A step
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
 * recorded by `recorder`. */
export function runStep(call: ProcessCall, recorder: Recorder | null = null, limitMs: number = stepTimeoutMs): StepRun {
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
    record: p.record,
  };
}
export { refusalEnd };
/** A step's refusal record, without its end line, or null where the step
 * succeeded. A refusal is the exit status and the first line's prefix its
 * tool's protocol states (`stage-execution.mts`), and a last line
 * `end of refusal`, so a record cut short is none. Any other exit but 0 (no
 * output, an exception, a usage error, a file it could not read or write,
 * the verifier's 3) is a failure of the tool, no
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
  // The verifier still decides whether it can interpret the declarations
  // reached.
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

export type CheckProgress = (message: string, unitFinished: boolean) => void;
/** Acceptance is deliberately private to this module. A proposal alone cannot
 * construct the public verified outcome: both Lean phases must succeed. */
function checkUnowned(artifacts: string, source: string, tsconfigPath?: string, typescriptErrors: boolean = false,
    subtypeRounds?: number, units: UnitSelection = { omitted: [], select: null }, progress?: CheckProgress): Outcome {
  using directoryScope = withinRunDirectory(artifacts);
  // Every stage invocation's attempt, in order (`stages.mts`).
  const recorder = new Recorder(join(artifacts, invocationLog), progress);
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
    // Each function's unit as the pass names it (`name@offset`).
    const unitIds = parsedData.functions.map((f: unknown): [string, string] => {
      const pos = field(f, "namePos"), name = field(f, "name");
      const at: unknown = Array.isArray(pos) ? pos[0] : undefined;
      if (typeof at !== "number" || typeof name !== "string") throw Error("invalid function identity");
      return [name, `${name}@${at}`];
    });
    if (!("init" in parsedData) || !Array.isArray(parsedData.init))
      throw Error("parser omitted the module initialization");
    const initialization = parsedData.init.map((s: unknown): [number, number] => {
      if (!s || typeof s !== "object" || !("pos" in s) || !Array.isArray(s.pos) ||
          s.pos.length !== 2 || !s.pos.every((n: unknown) => typeof n === "number"))
        throw Error("invalid initialization statement position");
      return [s.pos[0], s.pos[1]];
    });
    if (!("modules" in parsedData) || !Array.isArray(parsedData.modules)) throw Error("parser omitted modules");
    phase = "proposal";
    return singlePass(recorder, artifacts, ast, snapshot, parsedData.modules.length > 0, subtypeRounds, functions, unitIds, initialization,
      (detail) => refusedByTypeScript(detail, refusedErrors), units);
  } catch (e) {
    return {
      status: "error",
      artifacts,
      phase,
      detail: messageOf(e),
    };
  }
}
/** The single pass over a parsed file (`verifier --file-worker 8`, with
 * the module-interface stages it needs), and its outcome. Each
 * unit's verdict is a line `{unit, members, accepted, depends}` or `{unit,
 * members, refusal}`; a unit counts as verified only with every unit it
 * depends on verified, a module unit (`module:<location>#<unit>`) only where
 * its own line is printed. The file is verified when every unit is; else its
 * outcome is its first unit's that is not, in the front's order (the
 * functions by position, then the initialization). A unit the pass refuses
 * is `unverified` (or `exhausted`), phase `search`; a refusal before any
 * unit's verdict (the pass's front, which computes the types) is
 * `unsupported`, phase `proposal`, but a direct obligation the front finds
 * not established or exhausted, which is a refused unit's; a stage over its
 * limit is an error. */
function singlePass(recorder: Recorder, artifacts: string, ast: string, fileKey: string, hasModules: boolean, subtypeRounds: number | undefined,
    functions: string[], unitIds: [string, string][], initialization: [number, number][], named: (detail: string) => string,
    units: UnitSelection): Outcome {
  // The names a check of one unit selects: each function's, and the
  // initialization's where it runs code.
  const all = [...new Set(functions), ...(initialization.length > 0 ? [":init"] : [])];
  // A selection's roots, the file's names it names; the verifier checks
  // them and every unit their verdicts rest on (`selectionClosure`). A
  // selection of every name is the whole file.
  const select = units.select;
  const roots = select === null ? all : all.filter((n) => select.includes(n));
  const names = roots.length === all.length ? "" : roots.join(",");
  let checked: CheckedUnits;
  try {
    checked = verifyByUnits(ast, fileKey, names, {
      mode: 8, fuel: searchDepth, rounds: subtypeRounds ?? 4096, force: [],
      work: join(artifacts, "interfaces"), invocation: { limitMs: stepTimeoutMs, force: false, recorder },
    }, hasModules);
  } catch (error) {
    const message = messageOf(error);
    return { status: "error", artifacts, phase: "check", units: null,
      detail: /timed-out|timeout-replayed/.test(message)
        ? `timeout: a module-interface stage did not finish within ${stepTimeoutMs / 1000} s: ${message}` : message };
  }
  const over = (execution: string): string =>
    `timeout: verifier --file-worker did not finish within ${stepTimeoutMs / 1000} s` +
      (execution === "timeout-replayed" ? " (an earlier attempt; TSCERT_RETRY_TIMEOUTS=1 runs it again)" : "");
  const failure = (part: WorkerPart, what: string): Outcome => ({ status: "error", artifacts, phase: "check", units: null,
    detail: `tool failure: verifier --file-worker ${what}: ${part.error?.message ?? (part.stderr.trim().split("\n")[0] || "no output")}` });
  // The preparation: over its limit, failed, refused (the pass's front),
  // or the units the selection checks.
  const { preparation } = checked.run;
  const preparationExecution = preparation.execution;
  if (preparationExecution === "timed-out" || preparationExecution === "timeout-replayed")
    return { status: "error", artifacts, phase: "check", units: null,
      detail: `${over(preparationExecution)}: its preparation of the file` };
  if (preparationExecution === "failed" || preparation.status === null) return failure(preparation, "failed preparing the file");
  if (preparation.status !== 0) {
    const refused = verifierRefusal({ code: preparation.status, out: preparation.stdout,
      detail: preparation.stderr.trim() || preparation.stdout.trim(), record: preparation.record }, "--file-worker");
    writeFileSync(join(artifacts, "pass.log"), preparation.stderr);
    if (refused === null) throw Error("tool failure: verifier --file-worker exited with status 0 and no preparation");
    return readDiagnostic(refused)?.kind === "direct-obligation"
      ? { status: refusalStatus(refused), artifacts, phase: "search", detail: named(refused), units: null }
      : { status: "unsupported", artifacts, phase: "proposal", detail: named(refused), units: null };
  }
  const prepared = decodeWorkerPrepared(wireText(Buffer.from(preparation.stdout), "verifier --file-worker").trim());
  const lines: string[] = prepared.established.map((u) =>
    JSON.stringify({ unit: u, members: [u], accepted: true, depends: [], elaboration: null, contracts: [] }));
  const log: string[] = [];
  for (const part of checked.run.parts) {
    const unit = prepared.selected.find((u) => u.unit === part.part);
    if (unit === undefined) throw Error(`tool failure: verifier --file-worker answered ${part.part ?? "its preparation"}, no unit it selects`);
    if (part.execution === "timed-out" || part.execution === "timeout-replayed") {
      // A unit over its limit: its own refusal.
      lines.push(JSON.stringify({ unit: unit.unit, members: unit.members, refusal: over(part.execution), elaboration: null,
        contracts: [] }));
      log.push(`unit ${unit.unit}: ${over(part.execution)}`);
      continue;
    }
    if (part.execution === "failed" && part.error?.message.startsWith("memory limit") === true) {
      // A unit over the memory limit: no verdict, its failure said.
      log.push(`unit ${unit.unit}: tool failure: ${part.error.message}`);
      continue;
    }
    if (part.execution === "failed") return failure(part, `failed checking ${unit.unit}`);
    const line = wireText(Buffer.from(part.stdout), "verifier --file-worker").trim();
    lines.push(line);
    log.push(line);
  }
  writeFileSync(join(artifacts, "pass.log"), log.join("\n"));
  // The file's refusal beside its units': the first elaboration refusal
  // among the selected groups, as their units' lines state it, in the order
  // their checks run.
  const decoded = lines.map(decodeVerdictLine);
  const elaboration = decoded.map((l) => l.elaboration).find((e) => e !== null) ?? null;
  // The contracts each of the file's units' checks read, as its line records them.
  const contractReads: UnitContracts[] = decoded.filter((l, i) => !l.unit.startsWith("module:") &&
    decoded.findIndex((m) => m.unit === l.unit) === i).map((l) => ({ unit: l.unit, reads: [...l.contracts] }));
  const refusal = elaboration === null ? null : `reject: ${elaboration}`;
  // Where the module interfaces were not established, a unit refused at
  // ordinary contracts is refused for that first.
  const unestablished = checked.interfaceFailure === null ? null :
    `the module interfaces its imports read were not established: ${
      /timed-out|timeout-replayed/.test(checked.interfaceFailure)
        ? `timeout: a module-interface stage did not finish within ${stepTimeoutMs / 1000} s: ` : ""}${
      checked.interfaceFailure.split("\n")[0] ?? ""}`;
  const strings = (value: unknown): string[] => {
    if (!Array.isArray(value) || !value.every((x): x is string => typeof x === "string"))
      throw Error("tool failure: the single pass printed a unit without its members or dependencies");
    return value;
  };
  const verdicts = lines.map((line) => {
    const value: unknown = JSON.parse(line);
    const unit = field(value, "unit"), reason = field(value, "refusal");
    if (typeof unit !== "string") throw Error("tool failure: the single pass printed a verdict without its unit");
    const accepted = field(value, "accepted") === true;
    if (!accepted && typeof reason !== "string")
      throw Error("tool failure: the single pass printed a verdict without its refusal");
    return { unit, members: strings(field(value, "members")), accepted,
      depends: accepted ? strings(field(value, "depends")) : [],
      refusal: typeof reason === "string" ? (unestablished === null ? reason : `${unestablished}\nat ordinary contracts: ${reason}`)
        : "" };
  }).filter((v, i, all) => all.findIndex((w) => w.unit === v.unit) === i);
  // A unit's dependencies are decided by what it reaches through them, so a
  // cycle of units is decided together: a unit refused of its own, or one
  // with no verdict, the file's or a module's, refuses every unit reaching
  // it, by the first dependency on a shortest path to it; otherwise it is
  // verified.
  const byUnit = new Map(verdicts.map((v) => [v.unit, v]));
  const ownRefused = (u: string): boolean => {
    const w = byUnit.get(u);
    return w === undefined || !w.accepted;
  };
  type Reach = { root: string; via: string } | { verified: true };
  const reach = (unit: string): Reach => {
    const via = new Map<string, string>([[unit, unit]]);
    const queue = [unit];
    for (let k = 0; k < queue.length; k++) {
      const u = queue[k] ?? "";
      const w = byUnit.get(u);
      if (u !== unit && ownRefused(u)) return { root: u, via: via.get(u) ?? u };
      if (w === undefined) continue;
      for (const d of w.depends) {
        if (via.has(d)) continue;
        via.set(d, u === unit ? d : (via.get(u) ?? d));
        queue.push(d);
      }
    }
    return { verified: true };
  };
  // A refusal whose record has a source-named summary (`presentObligation`):
  // that summary as an `obligation:` line, after the refusal's first line
  // and any `obligation:` line the pass states.
  const source = readFileSync(fileKey, "utf8");
  const described = (text: string): string => {
    const record = readDiagnostic(text);
    const summary = record === undefined ? undefined : presentObligation(record, source).summary;
    if (summary === undefined) return text;
    const lines = text.split("\n");
    if (lines.includes(`obligation: ${summary}`)) return text;
    let at = 1;
    while (at < lines.length && lines[at]?.startsWith("obligation: ")) at++;
    return [...lines.slice(0, at), `obligation: ${summary}`, ...lines.slice(at)].join("\n");
  };
  const place = (unit: string): number => unit === "init" ? Infinity : Number(/@(\d+)$/.exec(unit)?.[1] ?? Infinity);
  const results: UnitResult[] = verdicts.filter((v) => !v.unit.startsWith("module:"))
    .sort((a, b) => place(a.unit) - place(b.unit)).map((v): UnitResult => {
      if (ownRefused(v.unit))
        return { unit: v.unit, members: v.members, status: refusalStatus(`reject: ${described(v.refusal)}`),
          phase: "search", detail: `reject: ${described(v.refusal)}`, depends: [] };
      const r = reach(v.unit);
      if ("verified" in r)
        return { unit: v.unit, members: v.members, status: "verified", phase: "check",
          detail: "",
          depends: v.depends };
      // A unit open by a dependency: the dependency on its path, then the
      // refusal of the unit refused of its own that the path reaches.
      const detail = `reject: a unit it depends on is refused: ${r.via}\n${byUnit.has(r.root) ? described(byUnit.get(r.root)?.refusal ?? "") : `${r.root}: no verdict`}`;
      return { unit: v.unit, members: v.members, status: refusalStatus(detail), phase: "search", detail, depends: [] };
    });
  const first = results.find((u) => u.status !== "verified");
  if (first === undefined && refusal === null)
    return { status: "verified", artifacts, phase: "check", functions, initialization, units: results, contractReads };
  if (first === undefined)
    return { status: "unsupported", artifacts, phase: "proposal", detail: named(refusal ?? ""), units: results,
      contractReads };
  return { status: first.status === "verified" ? "error" : first.status, artifacts, phase: "search", detail: first.detail,
    units: results, contractReads };
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
  const reads = "contractReads" in value ? { contractReads: readUnitContracts(value.contractReads) } : {};
  if (status === "verified" && phase === "check" && "functions" in value && Array.isArray(value.functions) &&
      value.functions.every((f: unknown) => typeof f === "string") && "initialization" in value &&
      Array.isArray(value.initialization) && value.initialization.every(isSpan))
    return { status, artifacts, phase, functions: value.functions, initialization: value.initialization,
      ...(units === undefined ? {} : { units: readUnitResults(units) }), ...reads };
  if ((status === "unsupported" || status === "unverified" || status === "exhausted" || status === "error") &&
      "detail" in value && typeof value.detail === "string")
    return { status, artifacts, phase, detail: value.detail,
      ...(units === undefined ? {} : { units: units === null ? null : readUnitResults(units) }), ...reads };
  throw Error("not an outcome");
}
/** Each unit's contract reads (`UnitContracts`), read field by field. */
function readUnitContracts(value: unknown): UnitContracts[] {
  if (!Array.isArray(value)) throw Error("not an outcome: its contract reads are no list");
  return value.map((u: unknown): UnitContracts => {
    const unit = field(u, "unit"), reads = field(u, "reads");
    if (typeof unit !== "string" || !Array.isArray(reads)) throw Error("not an outcome: a unit's contract reads are malformed");
    return { unit, reads: reads.map((r: unknown) => decodeContractRead(r, "an outcome's contract read")) };
  });
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
  retainArtifacts: boolean; units: UnitSelection; progress: boolean };
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
    retainArtifacts: value.retainArtifacts, units, progress: field(value, "progress") === true };
}
const checkRequest = (r: Request): Outcome =>
  checkUnowned(r.artifacts, r.source, r.project ? tsconfigOf(r.project) : undefined, r.typescriptErrors, r.subtypeRounds,
    r.units, r.progress ? (progress, unitFinished) => { process.send?.({ progress, unitFinished }, () => {}); } : undefined);

/** A whole check is killed after this long: the parser runs inside the worker,
 * so its step has no limit of its own. */
const checkTimeoutMs = 4 * stepTimeoutMs;
type Job = { request: Omit<Request, "artifacts">; done: (o: Outcome) => void; fail: (e: Error) => void; progress?: CheckProgress };
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
    const progress = field(message, "progress"), unitFinished = field(message, "unitFinished");
    if (typeof progress === "string" && typeof unitFinished === "boolean") {
      job.progress?.(progress, unitFinished);
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
  // A check that runs each unit on its own is bounded by its steps' limits alone.
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
    subtypeRounds?: number, retainArtifacts: boolean = false, units: UnitSelection = { omitted: [], select: null },
    progress?: CheckProgress):
    Promise<Outcome & Disposable> {
  runRoot();
  requireDiskSpace();
  return new Promise<Outcome>((done, fail) => {
    queue.push({ request: { source, project, typescriptErrors, subtypeRounds, retainArtifacts, units, progress: progress !== undefined },
      done, fail, progress });
    dispatch();
  }).then(result => ownedRun(result, retainArtifacts));
}
/** A row of the [trust surface](../docs/DESIGN.md#trust-surface): its table
 * and the opening words of its assumption. */
export type TrustRow = { table: "Trusted tools" | "Assumed values" | "Assumed of the host"; row: string };
/** The reviewed texts a check's declarations are read through, each with
 * the trust row stating its trust: where the overlay or rule is stated, as
 * the row's last cell names it (its code names, and the file or section
 * holding them), and that row. */
export type ContractOverlay = "intrinsics" | "arrayPrototype" | "primitivePrototypes" | "functionPrototype" |
  "collectionPrototypes" | "libraryGlobals" | "nodeGlobals" | "globalBinding" | "libraryModules" | "libraryTypes" |
  "dom" | "regexp" | "hostFamily" | "ambient" | "imported";
export const contractOverlays: Readonly<Record<ContractOverlay, { stated: { names: readonly string[]; in: string | null }; trust: TrustRow }>> = {
  intrinsics: { stated: { names: [], in: "tools/intrinsics.mts" },
    trust: { table: "Assumed values", row: "The intrinsics meet their signatures" } },
  arrayPrototype: { stated: { names: ["overlay"], in: "tools/array-prototype.mts" },
    trust: { table: "Assumed values", row: "`Array.prototype` meets `ArrayProto`" } },
  primitivePrototypes: { stated: { names: ["primitiveOverlay"], in: "tools/array-prototype.mts" },
    trust: { table: "Assumed values", row: "`String.prototype`, `Number.prototype`, `BigInt.prototype` and `Boolean.prototype` meet" } },
  functionPrototype: { stated: { names: ["functionOverlay"], in: "tools/array-prototype.mts" },
    trust: { table: "Assumed values", row: "`Function.prototype.toString` meets `FunctionProto`" } },
  collectionPrototypes: { stated: { names: ["interfaceOverlay"], in: "tools/array-prototype.mts" },
    trust: { table: "Assumed values", row: "`Set.prototype`, `Map.prototype` and `Date.prototype` hold the listed natives" } },
  libraryGlobals: { stated: { names: ["globalsOverlay"], in: "tools/library-globals.mts" },
    trust: { table: "Assumed values", row: "Each standard library global meets its reviewed overlay entry" } },
  nodeGlobals: { stated: { names: ["globalsOverlay"], in: "tools/library-globals.mts" },
    trust: { table: "Assumed values", row: "Node's `process` and `console` meet their reviewed entries" } },
  globalBinding: { stated: { names: ["GLOBAL", "selectGlobal"], in: null },
    trust: { table: "Assumed values", row: "A global variable's binding holds the value its reviewed entries describe" } },
  libraryModules: { stated: { names: ["modulesOverlay"], in: "tools/library-modules.mts" },
    trust: { table: "Assumed values", row: "Each Node module function the overlay of library modules lists meets its entry" } },
  libraryTypes: { stated: { names: ["typesOverlay"], in: "tools/library-types.mts" },
    trust: { table: "Assumed values", row: "The host's values of each type the overlay of library types states meet its statement" } },
  dom: { stated: { names: ["typesOverlay"], in: "tools/library-types.mts" },
    trust: { table: "Assumed values", row: "The DOM's host objects a text-measurement client uses meet" } },
  regexp: { stated: { names: [], in: "tools/regexp.mts" },
    trust: { table: "Assumed of the host", row: "A native regex (what a regex literal evaluates to) keeps" } },
  hostFamily: { stated: { names: [], in: "HOST-FAMILIES.md#trust-rows" },
    trust: { table: "Assumed values", row: "A host family's stable members" } },
  ambient: { stated: { names: ["AMBIENT", "collectDeclarations"], in: null },
    trust: { table: "Assumed values", row: "An ambient declaration of the checked file" } },
  imported: { stated: { names: ["IMPORT", "OVERLOADS"], in: "SOURCE-CONTRACTS.md" },
    trust: { table: "Assumed values", row: "An imported value meets its declaration" } },
};
/** The overlay owning each namespace of the declaration identities the
 * reader states (`tscert/<namespace>/…`), which no source declares. */
export const contractNamespaces: ReadonlyMap<string, ContractOverlay | "instance"> = new Map<string, ContractOverlay | "instance">([
  ["intrinsics", "intrinsics"], ["array-prototype", "arrayPrototype"], ["array-conversion", "arrayPrototype"],
  ...primitiveKinds.map((kind): [string, ContractOverlay] => [`${kind}-prototype`, "primitivePrototypes"]),
  ["function-prototype", "functionPrototype"], ["collections", "collectionPrototypes"], ["json", "libraryGlobals"],
  ["crypto", "libraryModules"], ["node", "libraryTypes"], ["intl", "libraryTypes"], ["dom", "dom"],
  ["regexp", "regexp"], ["family", "hostFamily"],
  // A computed declaration's instance, `tscert/instance/<n>/<module>`: its declaration's.
  ["instance", "instance"],
]);

/** Where a declaration comes from, as its identity's module names it
 * (`DeclarationIdentity`). */
export type ContractOrigin = "checked file" | "project" | "standard library" | "package" | "reader" | "intrinsic" |
  "ambient";
/** One contract a check read (`ContractRead`, recorded by the verifier where
 * it reads it): a value of the declaration document by its binding, or a
 * member by the declaration whose row states it; where it comes from, and the
 * overlay and trust row its reading rests on, or null where none states one:
 * a member of a type of TypeScript's standard library or of a package, read
 * as its declaration states, or of a type of the project's own sources. */
export type ContractEntry = { kind: "value" | "member"; module: string; name: string; key: string | null;
  specifier: string | null; origin: ContractOrigin; overlay: ContractOverlay | null; trust: TrustRow | null;
  /** The type the declaration document states for it, the document the
   * check read (`statedType`): one line per signature of an overloaded
   * callable, else one. */
  type: string[] };
/** The contracts a check's verdict relies on, each unit's as its verdict
 * line records them (`UnitContracts`), each once; the members of the checked
 * file's own types are counted. */
export type Contracts = { entries: ContractEntry[]; ownMembers: number };

type Identity = { module: string; name: string };
/** The package a module inside `node_modules` belongs to, `@types/node`. */
const packageOf = (module: string): string | null => {
  const parts = module.split("/"), at = parts.lastIndexOf("node_modules");
  if (at < 0) return null;
  const scope = parts[at + 1] ?? "";
  return scope.startsWith("@") ? `${scope}/${parts[at + 2] ?? ""}` : scope;
};
/** A declaration's origin, by its identity's module: the client's absolute
 * path, `typescript/lib/…`, `tscert/…` for what the reader states, a path
 * into `node_modules` or one of the project's. */
function originOf(module: string): ContractOrigin {
  if (module.startsWith("/")) return "checked file";
  if (module.startsWith("typescript/lib/")) return "standard library";
  if (module.startsWith("tscert/")) return module === intrinsicModule ? "intrinsic" : "reader";
  return packageOf(module) === null ? "project" : "package";
}
/** The overlay owning a declaration the reader states, by its namespace. */
function namespaceOverlay(module: string): ContractOverlay | null {
  const [, namespace, ...rest] = module.split("/");
  const owner = contractNamespaces.get(namespace ?? "");
  if (owner !== "instance") return owner ?? null;
  return typeOverlay({ module: rest.slice(1).join("/"), name: "" });
}
/** The overlay a type is read through: its namespace's, for one the reader
 * states; the host family's, for its package's; the standard library's
 * interface overlays, for a library interface they list. */
function typeOverlay(id: Identity): ContractOverlay | null {
  if (id.module.startsWith("tscert/")) return namespaceOverlay(id.module);
  if (packageOf(id.module) === hostPackage.name) return "hostFamily";
  if (id.module.startsWith("typescript/lib/")) {
    if (interfaceOverlay.has(id.name)) return "collectionPrototypes";
    if (libraryRegExpNames.includes(id.name)) return "regexp";
  }
  return null;
}
/** The origin a global's declaration has as `globalsOverlay`'s entries name
 * it: `library`, or the package declaring it. */
const globalOrigin = (module: string): string => module.startsWith("typescript/lib/") ? "library" : packageOf(module) ?? module;
/** The overlay a value is read through, by the specifier its binding names
 * and its declaration. */
function valueOverlay(specifier: string, imported: string, local: string, id: Identity): ContractOverlay {
  if (specifier === intrinsicModule) return "intrinsics";
  if (specifier === "ambient") return "ambient";
  if (specifier === "global") {
    const origin = globalOrigin(id.module);
    if (!globalOrigins(globalsOverlay, local).has(origin)) return "globalBinding";
    return origin === "library" ? "libraryGlobals" : "nodeGlobals";
  }
  if (id.module.startsWith("tscert/")) return namespaceOverlay(id.module) ?? "imported";
  if (packageOf(id.module) === hostPackage.name) return "hostFamily";
  if (moduleEntries(specifier, imported).length > 0) return "libraryModules";
  return "imported";
}

/** The type a read contract has in the declaration document the check read
 * (`ContractRead`): a value's type at its binding; a member's, at its key in
 * the row of the declaration the record names, by its full identity, as the
 * document writes it (an object's field, an index signature admitting the
 * key, a class value's static, a part of an intersection, the prototype it
 * states, or a base an interface's heritage names), at the declaration's
 * parameters. Written as TypeScript writes a type (`typeText`), one line per
 * signature of an overloaded callable; a row the document lacks is said so. */
export function statedType(document: DeclarationDocument, read: ContractRead): string[] {
  const stated = statedTerms(document, read);
  if ("missing" in stated) return [stated.missing];
  const texts = new TypeTexts(document, "text");
  return stated.terms.flatMap((t) => texts.signatures(t, stated.parameters, stated.binders));
}
/** What the declaration document states for a read contract, `statedType`'s
 * lookup: the terms at it, with the parameters of the declaration holding a
 * member and the binders of a value's type, or why the document states none. */
type Stated = { terms: TypeTerm[]; parameters: string[]; binders: Binder[] } | { missing: string };
/** A binder of a generic value or signature, with its bound and default
 * where the document states one. */
type Binder = { name: string; bound: TypeTerm | null; default?: TypeTerm | null };
const definitionOf = (document: DeclarationDocument, id: DeclarationIdentity): TypeDefinition | undefined =>
  document.definitions.find((d) => d.declaration.module === id.module && d.declaration.name === id.name &&
    d.declaration.span[0] === id.span[0] && d.declaration.span[1] === id.span[1]);
function statedTerms(document: DeclarationDocument, read: ContractRead): Stated {
  const named = (id: DeclarationIdentity): TypeDefinition | undefined => definitionOf(document, id);
  if ("value" in read) {
    const local = read.value.local;
    const value = document.values.find((v) => v.binding.local === local);
    if (value === undefined) return { missing: "(no value of the declaration document binds it)" };
    return { terms: [value.type], parameters: [], binders: value.typeParams };
  }
  const { declaration, key } = read.member;
  const seen = new Set<TypeDefinition>();
  const find = (d: TypeDefinition): TypeTerm[] => {
    if (seen.has(d)) return [];
    seen.add(d);
    const inTerm = (t: TypeTerm): TypeTerm[] => {
      switch (t.k) {
        case "object": {
          const field = t.fields.find((f) => sameKey(f.name, key));
          if (field !== undefined) return [field.optional ? { k: "union", parts: [field.type, undefinedTerm], span: field.span } : field.type];
          if (typeof key === "string") {
            if (t.numberIndex && canonicalNumeric(key)) return [t.numberIndex.value];
            if (t.stringIndex) return [t.stringIndex.value];
          } else if (t.symbolIndex) return [t.symbolIndex.value];
          return t.prototype ? inTerm(t.prototype) : [];
        }
        case "constructor": return (t.statics ?? []).filter((f) => sameKey(f.name, key)).map((f) => f.type);
        case "intersection": return t.parts.flatMap(inTerm);
        case "reference": {
          const target = named(t.reference.target);
          return target === undefined ? [] : find(target);
        }
        default: return [];
      }
    };
    const own = d.expression === null ? [] : inTerm(d.expression);
    return own.length > 0 ? own : d.bases.flatMap(inTerm);
  };
  const definition = named(declaration);
  if (definition === undefined) return { missing: "(no definition of the declaration document has this identity)" };
  if (definition.expression === null) return { missing: "(read at its meaning: the document states no equation)" };
  const found = find(definition);
  if (found.length === 0) return { missing: "(the declaration's row in the document names no such key)" };
  return { terms: found, parameters: definition.parameters.map((p) => p.name), binders: [] };
}
const undefinedTerm: TypeTerm = { k: "atom", name: "undefined", span: [0, 0] };
const sameKey = (name: PropertyKey, key: string | { symbol: number }): boolean =>
  typeof name === "string" ? name === key : typeof key !== "string" && key.symbol === name.symbol;
const canonicalNumeric = (key: string): boolean => String(Number(key)) === key;
/** A member's key as written after its declaration's name: `.name`, a
 * string that is no identifier as `["…"]`, a symbol by its declaration. */
function keyText(document: DeclarationDocument, key: string | { symbol: number }): string {
  if (typeof key !== "string") return `[${document.symbols[key.symbol]?.name ?? `symbol ${key.symbol}`}]`;
  return /^[A-Za-z_$][A-Za-z0-9_$]*$/.test(key) ? `.${key}` : `[${JSON.stringify(key)}]`;
}

/** A signature of a callable term (`TypeTexts.parts`): its binders, whether
 * it constructs, its parameters and result as `callable` writes them, and
 * the frames `F` stands for in it, where signatures differing only in one
 * frame, the same at each of their callables, are one, else none. */
type SignaturePart = { binders: readonly string[]; constructs: Extract<TypeTerm, { k: "constructor" }> | null; body: string;
  frames: string[]; parameters: readonly string[] };
/** Type terms as TypeScript writes types, for a reader. A signature's
 * parameters are named by position (`p0`, `p1`, `...rest`), the document
 * naming none; its receiver is `this:` unless it is the declaration holding
 * it. The type TScert reads a term at keeps its own spellings: an array's
 * presence as `Dense<…>` or `Sparse<…>` (a readable array is plain), a
 * callable's normal-return frame as `Modifies<{…}, R>` where it changes a
 * location, by the region each change applies to, a fresh result as
 * `Fresh<R>` (ANNOTATIONS.md), a type guard's or assertion's promise as
 * TypeScript writes it, and a signature's preconditions in a comment after
 * its result, `/* requires … *\/`, over its positions (`this`, `p0`, …);
 * a callable's other postconditions and its throw's frame are not written.
 * In the `ts` mode every text is a TypeScript type: a frame or freshness
 * around a promise is a comment after it, and signatures differing only in
 * one frame bind it as `F extends Frame`, the frames it is one of in a
 * comment. */
class TypeTexts {
  private readonly document: DeclarationDocument;
  private readonly mode: "text" | "ts";
  constructor(document: DeclarationDocument, mode: "text" | "ts") {
    this.document = document;
    this.mode = mode;
  }
  /** The frames `effect` writes as `F` while `frames` is set, in order. */
  private frames: string[] | null = null;
  /** A term's signatures, each once (a scheme's signatures, an intersection
   * of callables), each written with `arrow` before its result; null for a
   * term that is no callable. */
  parts(t: TypeTerm, parameters: readonly string[], binders: readonly Binder[], arrow: string): SignaturePart[] | null {
    const callables: { binders: readonly string[]; s: Extract<TypeTerm, { k: "function" | "constructor" }> }[] = [];
    const collect = (u: TypeTerm, bs: readonly string[]): boolean => {
      if (u.k === "function" || u.k === "constructor") {
        callables.push({ binders: bs, s: u });
        return true;
      }
      if (u.k === "scheme") {
        const own = [...bs, ...u.binders.map((b) => this.binder(b, parameters, bs))];
        return u.signatures.every((s) => collect(s, own));
      }
      return u.k === "intersection" && u.parts.length > 0 && u.parts.every((p) => collect(p, bs));
    };
    if (!collect(t, binders.map((b) => this.binder(b, parameters, [])))) return null;
    const lines: { key: string; shape: string; part: SignaturePart }[] = [];
    for (const { binders: bs, s } of callables) {
      const concrete = this.callable(s, parameters, bs, arrow);
      this.frames = [];
      const shape = this.callable(s, parameters, bs, arrow);
      const frames = this.frames;
      this.frames = null;
      const [frame] = frames;
      const constructs = s.k === "constructor" ? s : null;
      if (frame !== undefined && frames.every((f) => f === frame)) {
        const key = `${bs.join(", ")}\n${shape}`;
        const group = lines.find((l) => l.part.frames.length > 0 && l.key === key);
        if (group === undefined) lines.push({ key, shape, part: { binders: bs, constructs, body: concrete, frames: [frame], parameters } });
        else if (!group.part.frames.includes(frame)) group.part.frames.push(frame);
      } else {
        const key = `${bs.join(", ")}\n${concrete}`;
        if (!lines.some((l) => l.part.frames.length === 0 && l.key === key))
          lines.push({ key, shape: concrete, part: { binders: bs, constructs, body: concrete, frames: [], parameters } });
      }
    }
    return lines.map(({ shape, part }) => part.frames.length <= 1 ? { ...part, frames: [] } : { ...part, body: shape });
  }
  /** A binder as TypeScript declares one: `S extends B = D`. */
  binder(b: Binder, ps: readonly string[], bs: readonly string[]): string {
    const bound = b.bound === null ? "" : ` extends ${this.text(b.bound, ps, bs, 0)}`;
    const dflt = b.default === undefined || b.default === null ? "" : ` = ${this.text(b.default, ps, bs, 0)}`;
    return `${b.name}${bound}${dflt}`;
  }
  /** A signature's binders as written before its parameters: in the `ts`
   * mode with `F` where it stands for several frames. */
  head(p: SignaturePart): string {
    const bs = this.mode === "ts" && p.frames.length > 1
      ? [...p.binders, `F extends Frame /* one of ${p.frames.join(", ")} */`] : p.binders;
    return bs.length > 0 ? `<${bs.join(", ")}>` : "";
  }
  /** A term, one line per signature of a callable with several. In the
   * text mode, signatures that differ only in one frame are one line,
   * `Modifies<F, …>` where it stands, followed by the frames `F` is. */
  signatures(t: TypeTerm, parameters: readonly string[], binders: readonly Binder[]): string[] {
    const parts = this.parts(t, parameters, binders, " => ");
    if (parts === null) return [this.text(t, parameters, binders.map((b) => b.name), 0)];
    return parts.map((p) => this.signature(p) + (this.mode === "text" && p.frames.length > 1 ? `, F one of ${p.frames.join(", ")}` : ""));
  }
  /** A signature as a type: its binders, then its parameters and result. */
  signature(p: SignaturePart): string {
    const signature = `${this.head(p)}${p.body}`;
    return p.constructs === null ? signature : this.construct(p.constructs, signature, p.parameters, p.binders);
  }
  /** A term at a precedence: 0 anywhere, 1 inside a union or intersection,
   * 2 as an array's element. */
  text(t: TypeTerm, ps: readonly string[], bs: readonly string[], at: number): string {
    const wrap = (text: string, level: number): string => at > level ? `(${text})` : text;
    switch (t.k) {
      case "atom":
        switch (t.name) {
          case "safeInt": return "SafeInt";
          case "nonHost": return "NonHost";
          case "nonHostObject": return "NonHostObject";
          case "function": return wrap("(...args: never) => unknown", 0);
          case "class": return wrap("abstract new (...args: never) => unknown", 0);
          default: return t.name;
        }
      case "literal": return t.name === "string" ? JSON.stringify(t.text) : t.text;
      case "unique": return `typeof ${this.document.symbols[t.symbol]?.name ?? `symbol ${t.symbol}`}`;
      case "union":
        if (t.parts.length === 0) return "never";
        return wrap(t.parts.map((p) => this.text(p, ps, bs, p.k === "union" ? 0 : 1)).join(" | "), 0);
      case "intersection":
        if (t.parts.length === 0) return "unknown";
        return wrap(t.parts.map((p) => this.text(p, ps, bs, p.k === "intersection" ? 0 : 1)).join(" & "), 0);
      case "array": {
        const text = `${t.readonly ? "readonly " : ""}${this.text(t.element, ps, bs, 2)}[]`;
        return presence(t.presence, t.presence === "readable" ? wrap(text, 1) : text);
      }
      case "tuple": {
        const parts = [...t.required.map((p) => this.text(p, ps, bs, 0)), ...t.optional.map((p) => `${this.text(p, ps, bs, 1)}?`),
          ...(t.rest === null ? [] : [`...${this.text(t.rest, ps, bs, 2)}[]`])];
        return presence(t.presence, `${t.readonly ? "readonly " : ""}[${parts.join(", ")}]`);
      }
      case "object": {
        const members = [
          ...t.fields.map((f) => `${f.readonly ? "readonly " : ""}${this.key(f.name)}${f.optional ? "?" : ""}: ${this.text(f.type, ps, bs, 0)}`),
          ...(t.stringIndex ? [`${t.stringIndex.readonly ? "readonly " : ""}[k: string]: ${this.text(t.stringIndex.value, ps, bs, 0)}`] : []),
          ...(t.numberIndex ? [`${t.numberIndex.readonly ? "readonly " : ""}[k: number]: ${this.text(t.numberIndex.value, ps, bs, 0)}`] : []),
          ...(t.symbolIndex ? [`${t.symbolIndex.readonly ? "readonly " : ""}[k: symbol]: ${this.text(t.symbolIndex.value, ps, bs, 0)}`] : []),
          ...t.calls.map((c) => this.callable(c, ps, bs, ": ")),
        ];
        return members.length === 0 ? "{}" : `{ ${members.join("; ")} }`;
      }
      case "function":
      case "constructor": return wrap(t.k === "constructor" ? this.construct(t, this.callable(t, ps, bs), ps, bs) : this.callable(t, ps, bs), 0);
      case "pack": return this.text(t.of, ps, bs, at);
      case "scheme": {
        const lines = this.signatures(t, ps, []);
        return wrap(lines.length === 1 ? lines.join("") : lines.map((l) => `(${l})`).join(" & "), 0);
      }
      case "callable": return "Function";
      case "self": return "this";
      case "parameter": return ps[t.index] ?? `parameter ${t.index}`;
      case "binder": return t.name;
      case "reference": {
        const args = t.args.map((a) => this.text(a, ps, bs, 0));
        return args.length > 0 ? `${t.reference.name}<${args.join(", ")}>` : t.reference.name;
      }
    }
  }
  /** A signature's parameters and result, `(this: R, p0: A, ...rest: E[]) => B`,
   * or with `arrow` `": "` as a call signature or a method writes them,
   * `(…): B`; a construct signature's `new` is `construct`'s. */
  callable(t: Extract<TypeTerm, { k: "function" | "constructor" }>, ps: readonly string[], bs: readonly string[],
      arrow: string = " => "): string {
    const receiver = t.k === "function" && t.receiver !== null && t.receiver.k !== "self" ? [`this: ${this.text(t.receiver, ps, bs, 0)}`] : [];
    const params = t.params.map((p, i) => `p${i}: ${this.text(p, ps, bs, 0)}`);
    const rest = t.rest === null ? [] : [`...rest: ${t.rest.k === "pack" ? this.text(t.rest.of, ps, bs, 0) : `${this.text(t.rest, ps, bs, 2)}[]`}`];
    const returned = this.text(t.result, ps, bs, 0);
    const promise = t.effect.promise;
    const promised = promise === null ? null :
      promise.guards ? `p${promise.guards.param} is ${returned}` : `asserts p${promise.asserts.param} is ${returned}`;
    let result: string;
    if (promised !== null && this.mode === "ts") {
      const around = this.effect(t.effect, "…");
      result = around === "…" ? promised : `${promised} /* ${around} */`;
    } else result = this.effect(t.effect, promised ?? returned);
    const requires = this.precondition(t.effect);
    if (requires !== null) result += ` /* requires ${requires} */`;
    return `(${[...receiver, ...params, ...rest].join(", ")})${arrow}${result}`;
  }
  /** A construct signature as a type, `new (…) => B`, with the static fields
   * of the class value its type states, `(new (…) => B) & { … }`. */
  construct(t: Extract<TypeTerm, { k: "constructor" }>, signature: string, ps: readonly string[], bs: readonly string[]): string {
    const statics = (t.statics ?? []).map((f) => `${f.readonly ? "readonly " : ""}${this.key(f.name)}: ${this.text(f.type, ps, bs, 0)}`);
    return statics.length === 0 ? `new ${signature}` : `(new ${signature}) & { ${statics.join("; ")} }`;
  }
  /** A signature's preconditions over its entry positions, `this` the
   * receiver and `p<i>` the `i`-th actual, as one conjunction: the kinds the
   * receiver's elements are of, then each fact (tools/fact-text.mts); null
   * where it has none. */
  precondition(e: CallEffect): string | null {
    const named = (slot: number): string => positionText(slot);
    const facts = [
      ...(e.requires === null ? [] : [`every element of this is ${e.requires.join(" | ")}`]),
      ...e.pre.map((f) => indexFact(factOf(f), named) ?? "true"),
    ];
    return facts.length === 0 ? null : facts.join(" && ");
  }
  /** A result with its normal return's frame and freshness: the changes
   * other than `keep`, by region, as `Modifies<{…}, R>`; a result the call
   * allocated as `Fresh<R>`. */
  effect(e: CallEffect, result: string): string {
    const normal = e.exits.normal;
    const fresh = normal.ensures.some((f) => typeof f === "object" && "operation" in f &&
      (("freshSpine" in f.operation.post && f.operation.post.freshSpine.x === 0) ||
       ("freshObject" in f.operation.post && f.operation.post.freshObject.x === 0) ||
       ("freshRegion" in f.operation.post && f.operation.post.freshRegion.x === 0)));
    const shown = fresh ? `Fresh<${result}>` : result;
    const changes = normal.frame.filter((c) => c.change !== "keep").map((c) => `${JSON.stringify(regionText(c.region))}: "${c.change}"`);
    const frame = changes.length === 0 ? "{}" : `{ ${changes.join("; ")} }`;
    if (this.frames !== null) {
      this.frames.push(frame);
      return `Modifies<F, ${shown}>`;
    }
    return changes.length === 0 ? shown : `Modifies<${frame}, ${shown}>`;
  }
  key(name: PropertyKey): string {
    if (typeof name !== "string") return `[${this.document.symbols[name.symbol]?.name ?? `symbol ${name.symbol}`}]`;
    return /^[A-Za-z_$][A-Za-z0-9_$]*$/.test(name) ? name : JSON.stringify(name);
  }
}
/** A fact of a declaration document as tools/fact-text.mts reads facts, the
 * shape the verifier's diagnostics decode to (tools/diagnostic.mts): the same
 * fact, its lists copied, a quantified fact's body variables as that decoder
 * states them (a projection's term at slot 0, a free term bare). */
function factOf(f: StatedFact): IndexFact {
  const term = (t: LinearTerm): FactTerm => ({ ...t, path: [...t.path] });
  const form = <V, W>(xs: readonly (readonly [V, Integer])[], to: (v: V) => W): [W, Integer][] => xs.map(([v, c]) => [to(v), c]);
  const shiftOf = (sh: { readonly terms: readonly (readonly [LinearTerm, Integer])[]; readonly offset: Integer }):
      { terms: [FactTerm, Integer][]; offset: Integer } => ({ terms: form(sh.terms, term), offset: sh.offset });
  const variable = (v: BodyVariable): FactVariable => {
    if (v === "index" || v === "elem") return v;
    if ("offset" in v) return { offset: { delta: v.offset.delta } };
    if ("project" in v) return { project: { kind: v.project.kind, slot: 0, path: [...v.project.path] } };
    if ("parallel" in v)
      return { parallel: { slot: v.parallel.slot, path: [...v.parallel.path], shift: shiftOf(v.parallel.shift),
        kind: v.parallel.kind, elemPath: [...v.parallel.elemPath] } };
    return term(v.free.t);
  };
  const body = (b: BodyFact): BodyFormula => {
    if ("guarded" in b) {
      const t = b.guarded.target;
      const target = "self" in t ? { self: { path: [...t.self.path] } }
        : { parallel: { slot: t.parallel.slot, path: [...t.parallel.path], shift: shiftOf(t.parallel.shift), elemPath: [...t.parallel.elemPath] } };
      return { guarded: { target, tag: b.guarded.tag, body: body(b.guarded.body) } };
    }
    if ("bodyEither" in b) return { either: { left: body(b.bodyEither.left), right: body(b.bodyEither.right) } };
    if ("either" in b) return { either: { left: body(b.either.left), right: body(b.either.right) } };
    return "le" in b ? { form: form(b.le.form, variable), bound: b.le.bound, ne: false } : { form: form(b.ne.form, variable), bound: b.ne.bound, ne: true };
  };
  if ("linear" in f) {
    const fact = f.linear.fact;
    return { linear: { fact: "le" in fact ? { le: { form: form(fact.le.form, term), bound: fact.le.bound } }
      : { ne: { form: form(fact.ne.form, term), bound: fact.ne.bound } } } };
  }
  if ("either" in f) return { either: { left: factOf(f.either.left), right: factOf(f.either.right) } };
  if ("guarded" in f) return { guarded: { ...f.guarded, path: [...f.guarded.path], body: factOf(f.guarded.body) } };
  if ("element" in f) return { element: { value: f.element.value, array: f.element.array, index: shiftOf(f.element.index) } };
  if ("every" in f) {
    const e = f.every;
    const bound = (b: { readonly base: LinearTerm | null; readonly offset: number }) =>
      ({ base: b.base === null ? null : term(b.base), offset: b.offset });
    return { every: { slot: e.slot, path: [...e.path], start: bound(e.start), stop: bound(e.stop), body: e.body.map(body) } };
  }
  if ("atIndex" in f) {
    const e = f.atIndex;
    return { atIndex: { slot: e.slot, path: [...e.path], index: shiftOf(e.index), guard: e.guard, body: body(e.body) } };
  }
  if ("apart" in f) return { apart: { ...f.apart, path: [...f.apart.path], otherPath: [...f.apart.otherPath] } };
  if ("spineApart" in f) return { spineApart: { ...f.spineApart, path: [...f.spineApart.path], otherPath: [...f.spineApart.otherPath] } };
  if ("elemSpineApart" in f) return { elemSpineApart: { ...f.elemSpineApart, path: [...f.elemSpineApart.path], otherPath: [...f.elemSpineApart.otherPath] } };
  // (the others hold positions and flags alone)
  return f;
}
const presence = (p: "dense" | "readable" | "sparse", text: string): string =>
  p === "dense" ? `Dense<${text}>` : p === "sparse" ? `Sparse<${text}>` : text;
/** A call's entry position: `this` the receiver, `p<i>` the `i`-th actual. */
const positionText = (x: number): string => x === 0 ? "this" : `p${x - 1}`;
const pathText = (x: number, fields: readonly string[]): string => [positionText(x), ...fields].join(".");
const regionKey = (k: string | { symbol: number }): string => typeof k === "string" ? k : `[symbol ${k.symbol}]`;
const selectorText = (s: Selector): string =>
  [s.value ? "values" : "", s.array ? "arrays" : "", s.view ? "views" : ""].filter((t) => t !== "").join(" and ");
/** A region of a frame (`Region`), by the call's entry positions. */
function regionText(r: Region): string {
  if (r === "all") return "all";
  if ("field" in r) return `${positionText(r.field.x)}.${regionKey(r.field.key)}`;
  if ("fields" in r) return `${positionText(r.fields.x)}.*`;
  if ("cells" in r) return `${positionText(r.cells.x)}[*]`;
  if ("cls" in r) return selectorText(r.cls);
  if ("path" in r) return `${pathText(r.path.x, r.path.fields)}.${regionKey(r.path.key)}`;
  if ("pathFields" in r) return `${pathText(r.pathFields.x, r.pathFields.fields)}.*`;
  if ("pathCells" in r) return `${pathText(r.pathCells.x, r.pathCells.fields)}[*]`;
  if ("elemSpines" in r) return `${pathText(r.elemSpines.x, r.elemSpines.fields)}[*] spines`;
  return `${pathText(r.spine.x, r.spine.fields)} spine`;
}

/** A contract placed by `contractsOf`, with the read it is of. */
type Placed = { entry: ContractEntry; read: ContractRead };
/** The contracts the verdict lines of a check recorded (`Outcome.contracts`),
 * each placed by its overlay: a value by its binding (`valueOverlay`); a
 * member of a value's declaration, the type the value is read at, by that
 * value's, as its overlay states the value's members; any other member by
 * its declaration (`typeOverlay`). Each with the type `document`, the
 * declaration document the check read, states for it (`statedType`). */
export function contractsOf(units: readonly UnitContracts[], document: DeclarationDocument): Contracts {
  const { placed, ownMembers } = placedContracts(units, document);
  return { entries: placed.map((p) => p.entry), ownMembers };
}
function placedContracts(units: readonly UnitContracts[], document: DeclarationDocument): { placed: Placed[]; ownMembers: number } {
  const reads = units.flatMap((u) => u.reads);
  const key = (r: ContractRead): string => JSON.stringify(r);
  const once = reads.filter((r, i) => reads.findIndex((q) => key(q) === key(r)) === i);
  const valueOverlays = new Map<string, ContractOverlay>();
  const placed: Placed[] = [];
  for (const r of once) {
    if (!("value" in r)) continue;
    const { module, name, specifier, imported, local } = r.value;
    const overlay = valueOverlay(specifier, imported, local, { module, name });
    valueOverlays.set(`${module}\n${name}`, overlay);
    placed.push({ read: r, entry: { kind: "value", module, name: local, key: null, specifier,
      origin: specifier === "ambient" ? "ambient" : originOf(module), overlay, trust: contractOverlays[overlay].trust,
      type: statedType(document, r) } });
  }
  let ownMembers = 0;
  for (const r of once) {
    if (!("member" in r)) continue;
    const { declaration: { module, name }, key: member } = r.member;
    const overlay = valueOverlays.get(`${module}\n${name}`) ?? typeOverlay({ module, name });
    if (overlay === null && originOf(module) === "checked file") { ownMembers++; continue; }
    placed.push({ read: r, entry: { kind: "member", module, name, key: keyText(document, member), specifier: null,
      origin: originOf(module), overlay, trust: overlay === null ? null : contractOverlays[overlay].trust,
      type: statedType(document, r) } });
  }
  return { placed, ownMembers };
}
/** Contracts in the order they are reported: by trust row, in the order of
 * `contractOverlays`, each row with where its overlay is stated; then those
 * no row states, by origin and module. */
type ContractGroup<T> = { items: T[] } & ({ trust: TrustRow; stated: string } | { origin: ContractOrigin; module: string });
function contractGroups<T>(items: readonly T[], entry: (t: T) => ContractEntry): ContractGroup<T>[] {
  const groups: ContractGroup<T>[] = [];
  for (const overlay of Object.keys(contractOverlays).filter((o): o is ContractOverlay => o in contractOverlays)) {
    const read = items.filter((t) => entry(t).overlay === overlay);
    if (read.length === 0) continue;
    const { stated, trust } = contractOverlays[overlay];
    const at = [stated.names.map((n) => `\`${n}\``).join(", "), stated.in ?? ""].filter((t) => t !== "").join(" in ");
    groups.push({ items: read, trust, stated: at });
  }
  const unstated = items.filter((t) => entry(t).trust === null);
  for (const origin of ["standard library", "package", "project", "reader", "checked file"] as const) {
    const read = unstated.filter((t) => entry(t).origin === origin);
    for (const module of [...new Set(read.map((t) => entry(t).module))].sort())
      groups.push({ items: read.filter((t) => entry(t).module === module), origin, module });
  }
  return groups;
}
/** The module a value is imported from, where its binding names one. */
const importedFrom = (e: ContractEntry): string | null => e.specifier !== null && e.specifier !== "global" &&
  e.specifier !== intrinsicModule && e.specifier !== "ambient" && e.specifier !== "prototype" ? e.specifier : null;
/** The contracts as text: by trust row, each with its overlay and the
 * values and members read through it, each with its stated type, then the
 * members no row states. */
export function contractsText(contracts: Contracts): string {
  const shown = (e: ContractEntry): string => {
    if (e.kind === "member") return `${e.name}${e.key ?? ""}`;
    const from = importedFrom(e);
    return from === null ? e.name : `${e.name} (${from})`;
  };
  const typed = (indent: string) => (e: ContractEntry): string[] => e.type.length === 1 ? [`${indent}${shown(e)}: ${e.type[0]}`]
    : [`${indent}${shown(e)}:`, ...e.type.map((t) => `${indent}    ${t}`)];
  const sorted = (es: readonly ContractEntry[]): ContractEntry[] => [...es].sort((a, b) =>
    a.kind === b.kind ? shown(a).localeCompare(shown(b)) : a.kind === "value" ? -1 : 1);
  const lines = ["Contracts the verdict relies on, by trust row (docs/DESIGN.md#trust-surface):"];
  let unstated = false;
  for (const group of contractGroups(contracts.entries, (e) => e)) {
    if ("trust" in group) lines.push(`- ${group.trust.table}: "${group.trust.row} …"`, `  stated by ${group.stated}`);
    else {
      if (!unstated) lines.push("No trust row: read as their declarations state");
      unstated = true;
      lines.push(`- ${group.origin}, ${group.module}:`);
    }
    lines.push(...sorted(group.items).flatMap(typed("  ")));
  }
  lines.push(`Members of the checked file's own types read: ${contracts.ownMembers}`);
  return lines.join("\n") + "\n";
}
/** The declarations opening `contractsDeclarations`' file: TScert's forms
 * as the aliases TypeScript reads them at, each with its meaning. */
const declarationsPreamble = [
  "// The contracts the verdict relies on, as TypeScript declarations (verify-source.mts --contracts=ts):",
  "// by trust row (docs/DESIGN.md#trust-surface), each value and member at the type the run's",
  "// declaration document states, parameters named by position. A module: its names shadow",
  "// the standard library's.",
  "export {};",
  "/** An array with an element at every index below its length (docs/ANNOTATIONS.md). */",
  "type Dense<A> = A;",
  "/** An array that may hold no element at an index below its length. */",
  "type Sparse<A> = A;",
  "/** A normal return's value holds an array spine or an object the call allocated. */",
  "type Fresh<R> = R;",
  "/** The regions of a call's entry positions (`this`, `p0`, …) a normal return may change, each with its change. */",
  "type Frame = { readonly [region: string]: string };",
  "/** A call that, on a normal return, changes previously allocated locations only as `F` states, and returns `R`. */",
  "type Modifies<F extends Frame, R> = R;",
  "/** A safe integer. */",
  "type SafeInt = number;",
  "/** Every value but a host object. */",
  "type NonHost = unknown;",
  "/** An ordinary object: no host object. */",
  "type NonHostObject = object;",
];
/** A name as a TypeScript identifier: itself where it is one, else its runs
 * of identifier characters joined by `_` (`%Iterate%` as `Iterate`). */
const identifierOf = (name: string): string => {
  if (/^[A-Za-z_$][\w$]*$/.test(name)) return name;
  const joined = name.split(/[^\w$]+/).filter((p) => p !== "").join("_");
  return /^[A-Za-z_$]/.test(joined) ? joined : `_${joined}`;
};
/** The contracts as a TypeScript declaration file, of the same records and
 * the same types as `contractsOf` (`statedTerms`): by trust row, as
 * `contractGroups` orders them, each opened by a comment naming the row and
 * where its overlay is stated; in each, a value as `declare function`, one
 * signature per overload, or `declare const` at its type, its name made an
 * identifier with the original in a comment; the members of one declaration
 * as one `interface` at that declaration's parameters, a callable member as
 * its methods, any other as a property. TScert's forms are the aliases of
 * `declarationsPreamble`. */
export function contractsDeclarations(units: readonly UnitContracts[], document: DeclarationDocument): string {
  const { placed, ownMembers } = placedContracts(units, document);
  const texts = new TypeTexts(document, "ts");
  /** A contract's declarations, each line written after `name` and its
   * binders as a method or a function, or as a property's type. */
  const declared = (read: ContractRead): { signatures: SignaturePart[] } | { type: string } | { missing: string } => {
    const stated = statedTerms(document, read);
    if ("missing" in stated) return stated;
    const parts = stated.terms.map((t) => texts.parts(t, stated.parameters, stated.binders, ": "));
    const signatures = parts.flatMap((p) => p ?? []);
    if (parts.every((p) => p !== null) && signatures.every((p) => p.constructs === null)) return { signatures };
    const lines = stated.terms.flatMap((t) => texts.signatures(t, stated.parameters, stated.binders));
    return { type: lines.length === 1 ? lines.join("") : lines.map((l) => `(${l})`).join(" & ") };
  };
  const lines = [...declarationsPreamble];
  for (const group of contractGroups(placed, (p) => p.entry)) {
    lines.push("", ...("trust" in group ? [`// ${group.trust.table}: "${group.trust.row} …"`, `// stated by ${group.stated}`]
      : [`// No trust row: ${group.origin}, ${group.module}, read as its declarations state`]));
    const values = group.items.filter((p) => p.entry.kind === "value").sort((a, b) => a.entry.name.localeCompare(b.entry.name));
    for (const { entry, read } of values) {
      const name = identifierOf(entry.name), from = importedFrom(entry);
      const notes = [...(name === entry.name ? [] : [entry.name]), ...(from === null ? [] : [`from ${JSON.stringify(from)}`])];
      const note = notes.length === 0 ? "" : ` // ${notes.join(", ")}`;
      const d = declared(read);
      if ("missing" in d) lines.push(`// ${entry.name}: ${d.missing}`);
      else if ("type" in d) lines.push(`declare const ${name}: ${d.type};${note}`);
      else lines.push(...d.signatures.map((p) => `declare function ${name}${texts.head(p)}${p.body};${note}`));
    }
    const members = group.items.flatMap((p) => "member" in p.read ? [{ entry: p.entry, member: p.read.member, read: p.read }] : []);
    const identity = (id: DeclarationIdentity): string => `${id.module}\n${id.name}\n${id.span[0]}\n${id.span[1]}`;
    const declarations = [...new Map(members.map((m) => [identity(m.member.declaration), m.member.declaration])).values()]
      .sort((a, b) => a.name.localeCompare(b.name));
    for (const declaration of declarations) {
      const parameters = definitionOf(document, declaration)?.parameters.map((p) => p.name) ?? [];
      lines.push(`/** Declared in ${declaration.module}. */`,
        `interface ${identifierOf(declaration.name)}${parameters.length > 0 ? `<${parameters.join(", ")}>` : ""} {`);
      const own = members.filter((m) => identity(m.member.declaration) === identity(declaration))
        .map((m) => ({ ...m, key: texts.key(m.member.key) })).sort((a, b) => a.key.localeCompare(b.key));
      for (const { key, read } of own) {
        const d = declared(read);
        if ("missing" in d) lines.push(`  // ${key}: ${d.missing}`);
        else if ("type" in d) lines.push(`  ${key}: ${d.type};`);
        else lines.push(...d.signatures.map((p) => `  ${key}${texts.head(p)}${p.body};`));
      }
      lines.push("}");
    }
  }
  lines.push("", `// Members of the checked file's own types read: ${ownMembers}`);
  return lines.join("\n") + "\n";
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
  // `--contracts` adds the contracts the verdict relies on, as its units'
  // verdict lines record them, each with its overlay and trust row
  // (`contractsOf`), to the outcome, and writes them by trust row to
  // standard error: as text, or with `--contracts=ts` as a TypeScript
  // declaration file (`contractsDeclarations`).
  const contracts = all.includes("--contracts=ts") ? "ts" : all.includes("--contracts") ? "text" : null;
  const args = all.filter((a) => a !== "--typescript-errors" && a !== "--contracts" && a !== "--contracts=ts");
  if (!(args.length === 1 || (args.length === 3 && args[1] === "--project"))) {
    process.stderr.write("usage: node verify-source.mts file.ts [--project tsconfig-or-directory] [--typescript-errors]" +
      " [--subtype-rounds n] [--omit f,g] [--contracts[=ts]]\n");
    process.exitCode = 2;
  } else {
    // The printed outcome names the run's directory, kept for inspection.
    keepRunDirectories();
    // The check's collections share a declaration session, released at its end.
    retainDeclarationSessions(true);
    try {
      const result = check(args[0], args[2] ? tsconfigOf(args[2]) : undefined, typescriptErrors, subtypeRounds, false,
        units);
      if (contracts !== null) {
        const reads = result.contractReads;
        const document = reads === undefined ? null : readFragmentFile(join(result.artifacts, "fragment.json")).declarations;
        const relied = reads === undefined || document === null ? null : contractsOf(reads, document);
        process.stdout.write(JSON.stringify({ ...result, contracts: relied }, null, 2) + "\n");
        process.stderr.write(reads === undefined || document === null || relied === null
          ? "Contracts: no unit's check recorded its reads\n"
          : contracts === "ts" ? contractsDeclarations(reads, document) : contractsText(relied));
      } else process.stdout.write(JSON.stringify(result, null, 2) + "\n");
      process.exitCode = result.status === "verified" ? 0 : 1;
    } catch (error) {
      process.stderr.write(messageOf(error) + "\n");
      process.exitCode = 1;
    } finally {
      retainDeclarationSessions(false);
    }
  }
}
