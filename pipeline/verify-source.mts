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
import { fieldOf, messageOf } from "../tools/thrown.mts";
import { keepRunDirectories, ownedRun, requireDiskSpace, runDirectory, runRoot, withinRunDirectory } from "./run-directory.mts";
import type { Json as ParsedJson } from "../tools/calculus.mts";
import type { Ast } from "../tools/fragment.mts";
import { initOmission } from "../tools/fragment-parse.mts";
import { requireWellFormed, wireText } from "../tools/wire-strings.mts";
import { resolvableDeclaration } from "../tools/intrinsics.mts";
import { currentStore, invokeInProcess, invokeProcess, Recorder, readInvocationLog, type AttemptRecord } from "./stages.mts";
import { verifyWithInterfaces } from "./module-interfaces.mts";
import { refusalEnd, verifier, verifierProtocol, type ProcessCall, type Protocol } from "./stage-execution.mts";

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
    phase = "proposal";
    return singlePass(recorder, artifacts, ast, snapshot, subtypeRounds, functions, initialization,
      (detail) => refusedByTypeScript(detail, refusedErrors));
  } catch (e) {
    return {
      status: "error",
      artifacts,
      phase,
      detail: messageOf(e),
    };
  }
}
/** The single pass over a parsed file (`verifier --verify-interface-stage
 * 8`, with the module-interface stages it needs), and its outcome. Each
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
function singlePass(recorder: Recorder, artifacts: string, ast: string, fileKey: string, subtypeRounds: number | undefined,
    functions: string[], initialization: [number, number][], named: (detail: string) => string): Outcome {
  let run: StepRun;
  try {
    const invoked = verifyWithInterfaces(ast, fileKey, "", {
      mode: 8, fuel: searchDepth, rounds: subtypeRounds ?? 4096, force: [],
      work: join(artifacts, "interfaces"), invocation: { limitMs: stepTimeoutMs, force: false, recorder },
    }).run;
    const execution = invoked.record.execution;
    if (execution === "timed-out" || execution === "timeout-replayed")
      return { status: "error", artifacts, phase: "check", units: null,
        detail: `timeout: verifier --verify-interface-stage did not finish within ${stepTimeoutMs / 1000} s` +
          (execution === "timeout-replayed" ? " (an earlier attempt; TSCERT_RETRY_TIMEOUTS=1 runs it again)" : "") };
    if (invoked.error || invoked.signal || invoked.status === null)
      return { status: "error", artifacts, phase: "check", units: null,
        detail: `tool failure: verifier --verify-interface-stage ${invoked.signal ? `was killed by ${invoked.signal}` : "did not run"}: ` +
          `${invoked.error?.message ?? (invoked.stderr.trim().split("\n")[0] || "no exit status")}` };
    const out = wireText(invoked.stdoutBytes, "verifier --verify-interface-stage");
    const err = wireText(invoked.stderrBytes, "verifier --verify-interface-stage");
    run = { code: invoked.status, out, detail: err.trim() || out.trim(), record: invoked.record };
  } catch (error) {
    const message = messageOf(error);
    return { status: "error", artifacts, phase: "check", units: null,
      detail: /timed-out|timeout-replayed/.test(message)
        ? `timeout: a module-interface stage did not finish within ${stepTimeoutMs / 1000} s: ${message}` : message };
  }
  writeFileSync(join(artifacts, "pass.log"), run.detail);
  const lines = run.out.split("\n").filter((l) => l.startsWith("{"));
  const refusal = verifierRefusal(run, "--verify-interface-stage");
  if (refusal !== null && lines.length === 0)
    return readDiagnostic(refusal)?.kind === "direct-obligation"
      ? { status: refusalStatus(refusal), artifacts, phase: "search", detail: named(refusal), units: null }
      : { status: "unsupported", artifacts, phase: "proposal", detail: named(refusal), units: null };
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
    if (!accepted && typeof reason !== "string") throw Error("tool failure: the single pass printed a verdict without its refusal");
    return { unit, members: strings(field(value, "members")), accepted, depends: accepted ? strings(field(value, "depends")) : [],
      refusal: typeof reason === "string" ? reason : "" };
  });
  // A unit is closed when it and every unit it depends on are accepted.
  const byUnit = new Map(verdicts.map((v) => [v.unit, v]));
  const closed = new Map(verdicts.map((v) => [v.unit, v.accepted]));
  const openBy = new Map<string, string>();
  for (let changed = true; changed; ) {
    changed = false;
    for (const v of verdicts) {
      if (closed.get(v.unit) !== true) continue;
      const open = v.depends.find((d) => closed.get(d) === false || (d.startsWith("module:") && !byUnit.has(d)));
      if (open === undefined) continue;
      closed.set(v.unit, false);
      openBy.set(v.unit, open);
      changed = true;
    }
  }
  const place = (unit: string): number => unit === "init" ? Infinity : Number(/@(\d+)$/.exec(unit)?.[1] ?? Infinity);
  const results: UnitResult[] = verdicts.filter((v) => !v.unit.startsWith("module:"))
    .sort((a, b) => place(a.unit) - place(b.unit)).map((v): UnitResult => {
      if (closed.get(v.unit) === true)
        return { unit: v.unit, members: v.members, status: "verified", phase: "check", detail: "", depends: v.depends };
      // A unit open by a dependency: that dependency, then the refusal it
      // rests on, followed through the dependencies open in turn.
      const cause = (unit: string): string => {
        const seen = new Set<string>();
        let u: string | undefined = unit;
        while (u !== undefined && !seen.has(u)) {
          seen.add(u);
          const d = byUnit.get(u);
          if (d === undefined) return `${u}: no verdict`;
          if (!d.accepted) return d.refusal;
          u = openBy.get(u);
        }
        return "";
      };
      const open = openBy.get(v.unit) ?? "";
      const reason = cause(open);
      const detail = v.accepted ? `reject: a unit it depends on is refused: ${open}${reason === "" ? "" : `\n${reason}`}`
        : `reject: ${v.refusal}`;
      return { unit: v.unit, members: v.members, status: refusalStatus(detail), phase: "search", detail, depends: [] };
    });
  const first = results.find((u) => u.status !== "verified");
  if (first === undefined && refusal === null)
    return { status: "verified", artifacts, phase: "check", functions, initialization, units: results };
  if (first === undefined)
    return { status: "unsupported", artifacts, phase: "proposal", detail: named(refusal ?? ""), units: results };
  return { status: first.status === "verified" ? "error" : first.status, artifacts, phase: "search", detail: first.detail,
    units: results };
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
