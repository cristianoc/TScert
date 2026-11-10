// The common invocation mechanism of the pipeline's stages (DESIGN.md, "The
// stage store"): its replay policy, outside every key. Every stage of
// `verify-source.mts` and every control of the suites runs through
// `invokeProcess` or `invokeInProcess`: an invocation is bound by its
// execution adapter (`stage-execution.mts` for a process stage,
// `in-process-execution.mts` for an in-process one), whose description
// keys it, and its attempt is recorded (its input description, timing,
// limit, outcome and, where its dependencies are identified, its complete
// stage key). This module decides whether a replay-eligible invocation of a
// replayed stage returns an entry the store (`stage-store.mts`) holds at its
// key, reuses a timeout observed there, or executes through its adapter, and
// publishes what an execution produced.
//   node pipeline/stages.mts clean [--forget-host=<host>]…
//                                     removes entries, timeout observations and unheld snapshots,
//                                     the named hosts' owners counting as stopped
//   node pipeline/stages.mts evict    one eviction pass within TSCERT_STORE_BUDGET, its summary printed
import { spawn, spawnSync } from "node:child_process";
import { randomUUID } from "node:crypto";
import { appendFileSync, rmSync } from "node:fs";
import { homedir } from "node:os";
import { join, resolve } from "node:path";
import { readMeasurement, Store, type Cpu, type Measurement, type StoredResult } from "./stage-store.mts";
import { inputRead, isOperation, observationsHold, type Observation } from "../tools/files.mts";
import { liveCompilers, observeCompilers, type LiveCompiler } from "../tools/compiler-processes.mts";
import { bindProcess, codeFailure, deliver, executeProcess, executionDirectory, processCode, isStageName, readOrAbsent, resourcePolicy, runnerBuild, sha256, stageNames, text,
  type Canonical, type ProcessCall, type StageName } from "./stage-execution.mts";
import { bindInProcess, observedInput, runInProcess, type InProcessCall } from "./in-process-execution.mts";

export type { Cpu, Measurement } from "./stage-store.mts";

/** The stages that replay: every stage. A replayed check is the verifier's
 * result for exactly its key's inputs: the verifier's check mode reads the
 * three files its arguments name and prints its judgment, and reads no clock,
 * randomness, environment or working directory (DESIGN.md, the trust
 * surface). The parse and TypeScript's diagnostics are observed stages, keyed
 * by the file system's answers to their reads (STAGE-STORE.md, "Observed
 * stages"). */
const replayedStages: ReadonlySet<StageName> = new Set<StageName>(stageNames);

/** How an attempt ended: a finished result it computed (`executed`), one it
 * replayed, a timeout observation it reused, its own limit expiring, an
 * operational failure (a signal, an exit outside the stage's protocol, a
 * spawn failure) or an interruption of its run. */
export type Execution = "executed" | "replayed" | "timeout-replayed" | "timed-out" | "failed" | "interrupted";
const executions: readonly Execution[] = ["executed", "replayed", "timeout-replayed", "timed-out", "failed",
  "interrupted"];

/** What a replay measured, beside the stored attempt's own measurement. */
export type Replay = { lookupMs: number; validationMs: number; materializationMs: number; stored: Measurement };

/** One attempt of one stage invocation. */
export type AttemptRecord = {
  attempt: string;
  stage: StageName;
  /** The complete stage key, or null where the invocation is not
   * replay-eligible (`ineligible` says why). */
  key: string | null;
  ineligible: string | null;
  /** The invocation's input description: the key's preimage where it has
   * a key, its known inputs where it has none. */
  manifest: Canonical;
  /** Where a process stage ran: its program and its execution directory,
   * outside the key. */
  context: { program: string; directory: string } | null;
  forced: boolean;
  /** The enforced wall-clock limit, or null for a stage with none of its own. */
  limitMs: number | null;
  execution: Execution;
  exitStatus: number | null;
  /** Monotonic elapsed wall time of the attempt: its execution, or its
   * lookup, validation and materialization. For an interrupted attempt read
   * from a log, wall time from its start until the log is read. */
  elapsedMs: number;
  cpu: Cpu;
  replay: Replay | null;
};

/** The invocation records of one run, in the order the invocations started,
 * appended as JSON lines to `file` where one is given: a start event before
 * the stage runs and the attempt's record after it, so an attempt with a
 * start and no record was interrupted. */
export class Recorder {
  readonly records: AttemptRecord[] = [];
  private readonly file: string | null;
  constructor(file: string | null) {
    this.file = file;
  }
  start(record: AttemptRecord, startedAt: number): void {
    if (this.file) appendFileSync(this.file, JSON.stringify({ event: "start", record, startedAt }) + "\n");
  }
  finish(record: AttemptRecord): void {
    this.records.push(record);
    if (this.file) appendFileSync(this.file, JSON.stringify({ event: "end", record }) + "\n");
  }
}

/** The store setting: `TSCERT_STAGE_STORE` names the store's directory, or is
 * `off` to force execution; unset, the store is `$XDG_CACHE_HOME/tscert/stages`,
 * defaulting to `~/.cache/tscert/stages`. */
export function storeSetting(): { off: true } | { off: false; directory: string } {
  const named = process.env["TSCERT_STAGE_STORE"];
  if (named === "off") return { off: true };
  if (named) return { off: false, directory: resolve(named) };
  const cache = process.env["XDG_CACHE_HOME"] || join(homedir(), ".cache");
  return { off: false, directory: join(cache, "tscert", "stages") };
}
/** The store, or null where it is off. */
export function currentStore(): Store | null {
  const setting = storeSetting();
  return setting.off ? null : new Store(setting.directory);
}
/** The store's size budget in bytes: `TSCERT_STORE_BUDGET`, a number of
 * bytes with an optional K, M, G or T suffix (powers of 1024), by default
 * 15 GiB. */
export function storeBudget(): number {
  const named = process.env["TSCERT_STORE_BUDGET"];
  if (!named) return 15 * 1024 ** 3;
  const m = /^(\d+(?:\.\d+)?)([KMGT]?)$/i.exec(named.trim());
  if (!m) throw Error(`TSCERT_STORE_BUDGET is a number of bytes with an optional K, M, G or T suffix: ${named}`);
  return Math.floor(Number(m[1]) * 1024 ** " KMGT".indexOf((m[2] || " ").toUpperCase()));
}
/** Start an eviction pass of the store where one is due, in a detached
 * process of its own: the orchestrators (the case runner, the census, the
 * controls) call it as they start, and their run does not wait for it. */
export function startEviction(): void {
  const store = currentStore();
  if (!store?.evictionDue()) return;
  storeBudget(); // an invalid budget stops the orchestrator, where it is seen
  spawn(process.execPath, [import.meta.filename, "evict"], { detached: true, stdio: "ignore" }).unref();
}
/** Whether recorded timeouts are retried: `TSCERT_RETRY_TIMEOUTS=1` executes a
 * stage whose key holds a timeout observation and no finished result, at the
 * current limit, and replays finished results as before. */
export function retryingTimeouts(): boolean {
  return process.env["TSCERT_RETRY_TIMEOUTS"] === "1";
}

// ---------------------------------------------------------------------------
// Process stages

/** A process stage's result, its output bytes and their text, and its
 * attempt's record. */
export type Invoked = {
  status: number | null;
  signal: NodeJS.Signals | null;
  error: Error | undefined;
  stdoutBytes: Buffer;
  stderrBytes: Buffer;
  stdout: string;
  stderr: string;
  record: AttemptRecord;
};

export type InvokeOptions = {
  limitMs: number;
  /** Execute without consulting stored results or timeout observations. */
  force: boolean;
  recorder: Recorder | null;
};

/** How often a process waiting for another's execution of a key looks
 * again, and what it waits on. */
const claimPollMs = 50;
/** How long a process waits for another's claim of a key before reporting a tool failure: the stage's limit, after which the holder's execution is
 * killed, and as long again for its publication. */
export const claimWaitMs = (limitMs: number): number => 2 * limitMs;
const pause = new Int32Array(new SharedArrayBuffer(4));

/** Run a process stage through its adapter (`bindProcess`,
 * `executeProcess`). A replay-eligible invocation of a replayed stage, not
 * forced, replays a finished result stored at its key, or reports a timeout
 * observed there at a limit no smaller than its own unless timeouts are
 * retried (`retryingTimeouts`); executed, its finished result or its
 * timeout is published. */
export function invokeProcess(call: ProcessCall, options: InvokeOptions): Invoked {
  if (!Number.isSafeInteger(options.limitMs) || options.limitMs <= 0)
    throw Error("a process stage limit must be a positive integer number of milliseconds");
  const attempt = randomUUID();
  const started = performance.now();
  const startedAt = Date.now();
  const store = currentStore();
  const forced = options.force || store === null;
  let directory: string | null = null;
  let release: (() => void) | null = null;
  try {
    const bound = bindProcess(call);
    const { input } = bound;
    let ineligible = bound.ineligible;
    let key = ineligible === null ? sha256(input) : null;
    const record = (execution: Execution, exitStatus: number | null, replay: Replay | null, cpu: Cpu): AttemptRecord => ({
      attempt, stage: call.stage, key, ineligible, manifest: bound.manifest, context: directory === null ? null : { program: bound.program, directory },
      forced, limitMs: options.limitMs, execution, exitStatus, elapsedMs: performance.now() - started,
      cpu: replay ? replay.stored.cpu : cpu, replay,
    });
    options.recorder?.start(record("interrupted", null, null, { unavailable: "the attempt was interrupted" }), startedAt);
    const replaying = key !== null && store !== null && replayedStages.has(call.stage) ? { key, store } : null;
    // Within the store, one process executes a key at a time: another
    // process's execution of the same key is waited for, and its result
    // replayed (`Store.claim`). A wait outlasting the holder's own limit and
    // its grace (`claimWaitMs`) reports a failure without starting a second executor.
    const deadline = performance.now() + claimWaitMs(options.limitMs);
    for (let waited = 0; replaying && !forced; waited++) {
      if (waited > 0 && release === null) {
        if (performance.now() > deadline) {
          const error = new Error(`stage claim deadline exceeded for ${call.stage}`);
          const done = record("failed", null, null, { unavailable: "waiting for an execution claim" });
          options.recorder?.finish(done);
          return { status: null, signal: null, error, stdoutBytes: Buffer.alloc(0), stderrBytes: Buffer.alloc(0),
            stdout: "", stderr: "", record: done };
        }
        Atomics.wait(pause, 0, 0, claimPollMs);
      }
      const found = replaying.store.finished(call.stage, replaying.key, input);
      if (found) {
        const materializing = performance.now();
        deliver(bound, found.result.outputs);
        const done = record("replayed", found.result.exitStatus, { lookupMs: found.lookupMs,
          validationMs: found.validationMs, materializationMs: performance.now() - materializing,
          stored: found.result.measurement }, found.result.measurement.cpu);
        options.recorder?.finish(done);
        return { status: found.result.exitStatus, signal: null, error: undefined, stdoutBytes: found.result.stdout,
          stderrBytes: found.result.stderr, stdout: text(found.result.stdout), stderr: text(found.result.stderr),
          record: done };
      }
      const observed = retryingTimeouts() ? null
        : replaying.store.timeout(call.stage, replaying.key, input, options.limitMs, resourcePolicy);
      if (observed) {
        const { observation } = observed;
        const done = record("timeout-replayed", null, { lookupMs: observed.lookupMs, validationMs: 0,
          materializationMs: 0, stored: { attempt: observation.attempt, elapsedMs: observation.elapsedMs,
            limitMs: observation.limitMs, cpu: observation.cpu } }, observation.cpu);
        options.recorder?.finish(done);
        return { status: null, signal: null, error: undefined, stdoutBytes: Buffer.alloc(0), stderrBytes: Buffer.alloc(0),
          stdout: "", stderr: "", record: done };
      }
      if (release !== null) break;
      const claimed = replaying.store.claim(call.stage, replaying.key);
      if (claimed === "held") continue;
      release = claimed;
      // Recheck publication after acquiring: the preceding owner may have
      // published between our lookup and acquisition.
    }
    directory = executionDirectory(call.stage);
    const run = executeProcess(bound, directory, options.limitMs);
    const elapsedMs = performance.now() - started;
    ineligible ??= codeFailure(processCode);
    if (ineligible !== null) key = null;
    const done = record(run.ran, run.status, null, run.cpu);
    // The code that ran is the code the key names, or nothing is published.
    const publishing = replaying && key !== null ? replaying : null;
    if (publishing && run.ran === "executed")
      publishing.store.publishFinished(call.stage, publishing.key, { input, exitStatus: run.status, stdout: run.stdoutBytes,
        stderr: run.stderrBytes, outputs: run.produced, measurement: { attempt, elapsedMs, limitMs: options.limitMs,
          cpu: done.cpu } });
    if (publishing && run.ran === "timed-out")
      publishing.store.publishTimeout(call.stage, publishing.key, { input, attempt, elapsedMs, limitMs: options.limitMs,
        policy: resourcePolicy, cpu: done.cpu });
    release?.();
    release = null;
    options.recorder?.finish(done);
    return { status: run.status, signal: run.signal, error: run.error, stdoutBytes: run.stdoutBytes,
      stderrBytes: run.stderrBytes, stdout: run.stdout, stderr: run.stderr, record: done };
  } finally {
    release?.();
    if (directory !== null) rmSync(directory, { recursive: true, force: true });
  }
}

/** Whether an attempt ran its stage: executed, timed out or failed, not
 * replayed. */
export const ran = (record: AttemptRecord): boolean =>
  record.execution === "executed" || record.execution === "timed-out" || record.execution === "failed";

/** This process's control operations: how many executed and how many
 * replayed, and the wall time of those that executed. */
export const controlOperations: { executed: number; replayed: number; elapsedMs: number } =
  { executed: 0, replayed: 0, elapsedMs: 0 };

/** A control's run of the operation it tests (STAGE-STORE.md, "Controls"):
 * an invocation like any other, replayed where the store holds a finished
 * result for its key, and required to have run or to have replayed
 * that result; a replayed timeout is no run. */
export function tested(call: ProcessCall, limitMs: number = 30_000): Invoked {
  const invoked = invokeProcess(call, { limitMs, force: false, recorder: null });
  const { execution } = invoked.record;
  if (execution === "replayed") controlOperations.replayed++;
  else if (ran(invoked.record)) {
    controlOperations.executed++;
    controlOperations.elapsedMs += invoked.record.elapsedMs;
  } else throw Error(`control: ${call.stage} neither ran nor replayed a finished result (${execution})`);
  return invoked;
}

// ---------------------------------------------------------------------------
// In-process stages

/** The observations of a stored observed entry whose description is exactly
 * `manifest` with them, read field by field; null for any other entry. */
function storedObservations(input: string, manifest: { readonly [key: string]: Canonical }): Observation[] | null {
  let parsed: unknown;
  try {
    parsed = JSON.parse(input);
  } catch {
    return null;
  }
  const listed = typeof parsed === "object" && parsed !== null && "observations" in parsed ? parsed.observations : null;
  if (!Array.isArray(listed)) return null;
  const observations: Observation[] = [];
  for (const o of listed) {
    if (!Array.isArray(o) || o.length !== 3) return null;
    const [operation, path, answer]: unknown[] = o;
    if (!isOperation(operation) || typeof path !== "string" || !(answer === null || typeof answer === "string")) return null;
    observations.push([operation, path, answer]);
  }
  return observedInput(manifest, observations) === input ? observations : null;
}

/** The CPU time of in-process attempts, each attempt's own: a nested
 * attempt's time is its own and not its enclosing attempt's. Each attempt is
 * a frame of a stack. Its pipeline time is the process's (`process.cpuUsage`)
 * over the attempt but its nested attempts'. The compiler processes' time
 * goes to the innermost attempt running: a compiler process outlives an attempt where its
 * session is retained (`tools/declaration-session.mts`), so each is read by
 * the runner (`stage-runner --cpu`) at the start and end of each interval in
 * which the attempt is the innermost one, when it starts (from zero) and just before
 * it ends (`compiler-processes.mts`); the attempt adds the differences. A
 * process is named by its generation, which a reused process id does not
 * repeat. */
type Sample = { userMs: number; systemMs: number; peakBytes: number };
type Frame = {
  started: number;
  cpu: NodeJS.CpuUsage;
  /** The pipeline time of the attempts nested in this one, in microseconds. */
  nested: { user: number; system: number };
  userMs: number; systemMs: number; peakBytes: number | null; counted: number; unread: number;
  /** Each compiler's reading at the start of the current interval. */
  baseline: Map<number, Sample | null>;
  ended: boolean;
};
const frames: Frame[] = [];
/** A compiler process's CPU time and lifetime peak memory so far, or null
 * where it is not read. */
let failingReadings: number = 0;
/** Tests only: the next `count` readings are not taken. */
export function failCompilerReadingsForTests(count: number): void {
  failingReadings = count;
}
function sample(compiler: LiveCompiler): Sample | null {
  if (failingReadings > 0) {
    failingReadings--;
    return null;
  }
  const p = spawnSync(runnerBuild, ["--cpu", String(compiler.pid)], { encoding: "utf8" });
  const used = p.status === 0 ? /^cpu (\d+) (\d+) (\d+)\n$/.exec(p.stdout) : null;
  return used ? { userMs: Number(used[1]) / 1000, systemMs: Number(used[2]) / 1000, peakBytes: Number(used[3]) } : null;
}
const zero: Sample = { userMs: 0, systemMs: 0, peakBytes: 0 };
/** For the controls: by compiler generation, the CPU time the attempts
 * counted, and the process's last reading as it ended, its lifetime's. */
export const compilerAccounts: Map<number, { countedMs: number; lifetimeMs: number | null }> = new Map();
const accountOf = (generation: number): { countedMs: number; lifetimeMs: number | null } => {
  const account = compilerAccounts.get(generation) ?? { countedMs: 0, lifetimeMs: null };
  compilerAccounts.set(generation, account);
  return account;
};
/** Add a compiler's time between `from` and `to` to an attempt. */
function count(frame: Frame, generation: number, from: Sample | null, to: Sample | null): void {
  frame.counted++;
  if (from === null || to === null) {
    frame.unread++;
    return;
  }
  frame.userMs += to.userMs - from.userMs;
  frame.systemMs += to.systemMs - from.systemMs;
  frame.peakBytes = Math.max(frame.peakBytes ?? 0, to.peakBytes);
  accountOf(generation).countedMs += to.userMs - from.userMs + to.systemMs - from.systemMs;
}
/** The running compilers' readings. */
const readings = (): Map<number, Sample | null> =>
  new Map(liveCompilers().map((compiler) => [compiler.generation, sample(compiler)]));
/** End a frame's interval at `now` (a process that ended unannounced has no
 * reading, and counts as not read), or begin one. */
function closeInterval(frame: Frame, now: Map<number, Sample | null>): void {
  for (const [generation, from] of frame.baseline) count(frame, generation, from, now.get(generation) ?? null);
  frame.baseline.clear();
}
function openInterval(frame: Frame, now: Map<number, Sample | null>): void {
  frame.baseline = new Map(now);
}
/** The innermost attempt running. */
const counting = (): Frame | undefined => frames.at(-1);
observeCompilers({
  started: (compiler: LiveCompiler): void => {
    counting()?.baseline.set(compiler.generation, zero);
  },
  ending: (compiler: LiveCompiler): void => {
    const top = counting();
    if (!top || !top.baseline.has(compiler.generation)) return;
    const last = sample(compiler);
    accountOf(compiler.generation).lifetimeMs = last && last.userMs + last.systemMs;
    count(top, compiler.generation, top.baseline.get(compiler.generation) ?? null, last);
    top.baseline.delete(compiler.generation);
  },
});
/** An attempt's frame begun: its clocks started, then the interval of the
 * attempt it interrupts ended and its own begun at the same readings, where
 * a compiler runs. */
function beginFrame(): Frame {
  const frame: Frame = { started: performance.now(), cpu: process.cpuUsage(), nested: { user: 0, system: 0 },
    userMs: 0, systemMs: 0, peakBytes: null, counted: 0, unread: 0, baseline: new Map(), ended: false };
  const now = readings();
  const top = counting();
  if (top) closeInterval(top, now);
  openInterval(frame, now);
  frames.push(frame);
  return frame;
}
/** An attempt's frame ended: its interval closed and the enclosing attempt's
 * resumed at the same readings, and told of this attempt's pipeline time; the
 * attempt's own pipeline time, in microseconds. */
function endFrame(frame: Frame): NodeJS.CpuUsage {
  frame.ended = true;
  const at = frames.lastIndexOf(frame);
  if (at >= 0) frames.splice(at, 1);
  const now = readings();
  closeInterval(frame, now);
  const resumed = counting();
  if (resumed) openInterval(resumed, now);
  const inclusive = process.cpuUsage(frame.cpu);
  const parent = frames.at(-1);
  if (parent) {
    parent.nested.user += inclusive.user;
    parent.nested.system += inclusive.system;
  }
  return { user: inclusive.user - frame.nested.user, system: inclusive.system - frame.nested.system };
}

/** Run an in-process stage through its adapter (`bindInProcess`,
 * `runInProcess`), recording its attempt: an exception it throws is an
 * operational failure, recorded and thrown on. A replay-eligible invocation
 * of a replayed stage with a codec replays and publishes as a process stage
 * does. An observed stage replays a referenced entry whose observations hold
 * now, and is published where they are complete. */
export function invokeInProcess<T>(call: InProcessCall<T>, options: { force: boolean; recorder: Recorder | null }):
    { value: T; record: AttemptRecord } {
  const frame = beginFrame();
  enclosing.push(options);
  try {
    return attemptInProcess(call, options, frame);
  } finally {
    enclosing.pop();
    if (!frame.ended) endFrame(frame);
  }
}
/** The options of the in-process invocations running, innermost last. */
const enclosing: { force: boolean; recorder: Recorder | null }[] = [];
/** An in-process stage invoked while another runs, a parse's module stage:
 * forced where the enclosing invocation is, and recorded by its recorder. */
export function invokeNested<T>(call: InProcessCall<T>): { value: T; record: AttemptRecord } {
  return invokeInProcess(call, enclosing.at(-1) ?? { force: false, recorder: null });
}
function attemptInProcess<T>(call: InProcessCall<T>, options: { force: boolean; recorder: Recorder | null },
    frame: Frame): { value: T; record: AttemptRecord } {
  const attempt = randomUUID();
  const started = frame.started;
  const startedAt = Date.now();
  const store = currentStore();
  const forced = options.force || store === null;
  const { manifest, input, identityFailure } = bindInProcess(call);
  let ineligible = identityFailure();
  // An observed stage's manifest here is its pre-key's; its key is known
  // once its observations are.
  let key = ineligible === null ? sha256(input) : null;
  let recorded: Canonical = manifest;
  // The attempt's own record, at its end; the start event's, `interrupted`,
  // ends no frame.
  const record = (execution: Execution, replay: Replay | null): AttemptRecord => {
    const used = execution === "interrupted" ? process.cpuUsage(frame.cpu) : endFrame(frame);
    const measured: Cpu = frame.unread > 0
      ? { unavailable: `${frame.unread} of the attempt's ${frame.counted} compiler process readings were not read` }
      : { userMs: used.user / 1000 + frame.userMs, systemMs: used.system / 1000 + frame.systemMs,
        peakBytes: frame.peakBytes,
        covers: frame.counted > 0 ? "the pipeline's process and the compiler processes running during it"
          : "the pipeline's process" };
    return {
      attempt, stage: call.stage, key, ineligible, manifest: recorded, context: null, forced, limitMs: null, execution,
      exitStatus: null, elapsedMs: performance.now() - started, cpu: replay ? replay.stored.cpu : measured, replay,
    };
  };
  options.recorder?.start(record("interrupted", null), startedAt);
  const replaying = key !== null && store !== null && call.codec && replayedStages.has(call.stage)
    ? { key, store, codec: call.codec } : null;
  if (replaying && !forced) {
    const candidates = call.observed ? replaying.store.candidates("observed", call.stage, replaying.key) : [replaying.key];
    for (const candidate of candidates) {
      const found = replaying.store.finished(call.stage, candidate, call.observed ? null : input);
      if (!found) continue;
      let validationMs = found.validationMs;
      if (call.observed) {
        const validating = performance.now();
        const observations = storedObservations(found.result.input, manifest);
        // A named input's read answers as the invocation's own input does;
        // every other observation as the file system does now.
        const inputs = call.observed.inputs;
        const holds = observations !== null &&
          observations.every(([o, name, answer]) => o !== "input" || (inputs !== undefined && inputs(name) === answer)) &&
          observationsHold(observations.filter(([o]) => o !== "input"));
        validationMs += performance.now() - validating;
        if (!holds) continue;
        // The replayed value depends on the inputs it read, as an executed one
        // does: a process cache computing it keeps none.
        for (const [o, name] of observations) if (o === "input") inputRead(name);
        key = candidate;
        recorded = { ...manifest, observations: observations.length };
      }
      const materializing = performance.now();
      const value = replaying.codec.decode(found.result.stdout);
      const done = record("replayed", { lookupMs: found.lookupMs, validationMs,
        materializationMs: performance.now() - materializing, stored: found.result.measurement });
      options.recorder?.finish(done);
      return { value, record: done };
    }
  }
  let ran: ReturnType<typeof runInProcess<T>>;
  try {
    ran = runInProcess(call);
  } catch (error) {
    options.recorder?.finish(record("failed", null));
    throw error;
  }
  const { value, observations, incomplete } = ran;
  if (incomplete !== null) {
    ineligible ??= incomplete;
    key = null;
  }
  ineligible ??= identityFailure();
  if (ineligible !== null) key = null;
  let fullInput = input;
  if (call.observed && key !== null) {
    fullInput = observedInput(manifest, observations);
    key = sha256(fullInput);
    recorded = { ...manifest, observations: observations.length };
  }
  const done = record("executed", null);
  if (replaying && key !== null) {
    const result: StoredResult = { input: fullInput, exitStatus: 0, stdout: replaying.codec.encode(value),
      stderr: Buffer.alloc(0), outputs: [], measurement: { attempt, elapsedMs: done.elapsedMs, limitMs: null, cpu: done.cpu } };
    replaying.store.publishFinished(call.stage, key, result);
    if (call.observed) replaying.store.reference("observed", call.stage, replaying.key, key);
  }
  options.recorder?.finish(done);
  return { value, record: done };
}

// ---------------------------------------------------------------------------
// Records read back

/** Decode a manifest's JSON values. */
function readCanonical(value: unknown): Canonical {
  if (value === null || typeof value === "string" || typeof value === "boolean") return value;
  if (typeof value === "number" && Number.isFinite(value)) return value;
  if (Array.isArray(value)) return value.map((entry: unknown) => readCanonical(entry));
  if (typeof value === "object") {
    const fields: { [key: string]: unknown } = { ...value };
    return Object.fromEntries(Object.entries(fields).map(([key, entry]) => [key, readCanonical(entry)]));
  }
  throw Error("not a manifest JSON value");
}

/** An invocation record a run wrote, read field by field. */
export function readAttemptRecord(value: unknown): AttemptRecord {
  const fail = (): never => {
    throw Error(`not an attempt record: ${JSON.stringify(value)?.slice(0, 200)}`);
  };
  if (typeof value !== "object" || value === null) return fail();
  const v: { [key: string]: unknown } = { ...value };
  const fields = ["attempt", "stage", "key", "ineligible", "manifest", "context", "forced", "limitMs", "execution",
    "exitStatus", "elapsedMs", "cpu", "replay"];
  if (Object.keys(v).sort().join() !== [...fields].sort().join()) return fail();
  const nullableString = (x: unknown): x is string | null => x === null || typeof x === "string";
  const nullableNumber = (x: unknown): x is number | null => x === null || typeof x === "number";
  const { attempt, stage, key, ineligible, forced, limitMs, execution, exitStatus, elapsedMs } = v;
  const manifest = readCanonical(v["manifest"]);
  const found = executions.find((e) => e === execution);
  const measured = readMeasurement({ attempt: "", elapsedMs: 0, limitMs: null, cpu: v["cpu"] });
  if (typeof attempt !== "string" || !isStageName(stage) || !nullableString(key) || !nullableString(ineligible) ||
      typeof forced !== "boolean" || !nullableNumber(limitMs) || found === undefined ||
      !nullableNumber(exitStatus) || typeof elapsedMs !== "number" || !measured)
    return fail();
  const c = v["context"];
  let context: AttemptRecord["context"] = null;
  if (c !== null) {
    const f: { [key: string]: unknown } = typeof c === "object" && c !== null ? { ...c } : fail();
    const { program, directory } = f;
    if (Object.keys(f).sort().join() !== "directory,program" || typeof program !== "string" ||
        typeof directory !== "string")
      return fail();
    context = { program, directory };
  }
  const r = v["replay"];
  let replay: Replay | null = null;
  if (r !== null) {
    const f: { [key: string]: unknown } = typeof r === "object" && r !== null ? { ...r } : fail();
    const { lookupMs, validationMs, materializationMs } = f;
    const stored = readMeasurement(f["stored"]);
    if (Object.keys(f).sort().join() !== "lookupMs,materializationMs,stored,validationMs" ||
        typeof lookupMs !== "number" || typeof validationMs !== "number" || typeof materializationMs !== "number" ||
        !stored)
      return fail();
    replay = { lookupMs, validationMs, materializationMs, stored };
  }
  return { attempt, stage, key, ineligible, manifest, context, forced, limitMs, execution: found, exitStatus, elapsedMs,
    cpu: measured.cpu, replay };
}

/** The attempts of a run's invocation log (`Recorder`), in order; an attempt
 * started and never recorded is `interrupted`. */
export function readInvocationLog(file: string): AttemptRecord[] {
  const bytes = readOrAbsent(file);
  if (bytes === null) return [];
  const records: AttemptRecord[] = [];
  const open = new Map<string, number>();
  for (const line of bytes.toString("utf8").split("\n")) {
    if (line === "") continue;
    const event: unknown = JSON.parse(line);
    if (typeof event !== "object" || event === null) throw Error(`not an invocation event: ${line.slice(0, 200)}`);
    const e: { [key: string]: unknown } = { ...event };
    if (e["event"] === "start" && Object.keys(e).sort().join() === "event,record,startedAt" && typeof e["startedAt"] === "number" && Number.isFinite(e["startedAt"])) {
      const record = readAttemptRecord(e["record"]);
      open.set(record.attempt, records.length);
      records.push({ ...record, execution: "interrupted",
        elapsedMs: Math.max(record.elapsedMs, Date.now() - e["startedAt"]),
        cpu: { unavailable: "the attempt was interrupted" } });
    } else if (e["event"] === "end" && Object.keys(e).sort().join() === "event,record") {
      const record = readAttemptRecord(e["record"]);
      const at = open.get(record.attempt);
      if (at !== undefined) {
        records[at] = record;
        open.delete(record.attempt);
      } else records.push(record);
    } else throw Error(`not an invocation event: ${line.slice(0, 200)}`);
  }
  return records;
}

if (import.meta.filename === resolve(process.argv[1] ?? "") && (process.argv[2] === "clean" || process.argv[2] === "evict")) {
  const store = currentStore();
  if (!store) {
    process.stderr.write(`TSCERT_STAGE_STORE is off: there is no store to ${process.argv[2]}\n`);
    process.exitCode = 2;
  } else if (process.argv[2] === "clean") {
    const options = process.argv.slice(3);
    const forget = options.map((o) => /^--forget-host=(.+)$/.exec(o)?.[1]);
    if (forget.some((h) => h === undefined)) {
      process.stderr.write(`usage: node pipeline/stages.mts clean [--forget-host=<host>]…\n`);
      process.exitCode = 2;
    } else {
      store.clean(forget.filter((h) => h !== undefined));
      process.stdout.write(`cleaned ${store.root}\n`);
    }
  } else {
    const pass = store.evictionPass(storeBudget());
    process.stdout.write(pass ? JSON.stringify(pass) + "\n" : `another pass is running in ${store.root}\n`);
  }
}
