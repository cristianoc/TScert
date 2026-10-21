// The common invocation mechanism of the pipeline's stages (DESIGN.md, "The
// stage store"). Every stage of `verify-source.mts` and every control of the
// suites runs through `invokeProcess` or `invokeInProcess`: an invocation
// binds its input files by content into a fresh execution directory, runs
// with a fixed argument vector, working directory and environment, and
// records its attempt (timing, limit, outcome and, where its dependencies are
// identified, its complete stage key).
import { spawnSync } from "node:child_process";
import { createHash, randomUUID } from "node:crypto";
import { appendFileSync, readFileSync, realpathSync, rmSync, statSync, writeFileSync } from "node:fs";
import { arch, homedir, platform } from "node:os";
import { basename, dirname, join, resolve } from "node:path";
import { runDirectory } from "./run-directory.mts";

const here = import.meta.dirname;

/** The stages of the pipeline's entry point (DESIGN.md, "The stage store"). */
export type StageName = "parse" | "lower" | "propose" | "assemble" | "search" | "check" | "explain" | "diagnostics";
const stageNames: readonly StageName[] = ["parse", "lower", "propose", "assemble", "search", "check", "explain",
  "diagnostics"];
export const isStageName = (value: unknown): value is StageName => stageNames.some((s) => s === value);

/** The repository's builds of the two audited programs, at their build
 * locations: the Lean verifier and the OCaml producer. */
export const verifierBuild: string = resolve(here, "../lean/.lake/build/bin/verifier");
export const producerBuild: string = resolve(here, "../ocaml-producer/_build/default/producer.exe");

/** How an attempt ended: a finished result it computed (`executed`), one it
 * replayed, a timeout observation it reused, its own limit expiring, an
 * operational failure (a signal, an exit outside the stage's protocol, a
 * spawn failure) or an interruption of its run. */
export type Execution = "executed" | "replayed" | "timeout-replayed" | "timed-out" | "failed" | "interrupted";
const executions: readonly Execution[] = ["executed", "replayed", "timeout-replayed", "timed-out", "failed",
  "interrupted"];

/** CPU time, with the processes it covers, or why none is measured. */
export type Cpu = { userMs: number; systemMs: number; covers: string } | { unavailable: string };

/** One attempt of one stage invocation. */
export type AttemptRecord = {
  attempt: string;
  stage: StageName;
  /** The complete stage key, or null where the invocation is not
   * replay-eligible (`ineligible` says why). */
  key: string | null;
  ineligible: string | null;
  forced: boolean;
  /** The enforced wall-clock limit, or null for a stage with none of its own. */
  limitMs: number | null;
  execution: Execution;
  exitStatus: number | null;
  /** Monotonic elapsed wall time of the attempt. */
  elapsedMs: number;
  cpu: Cpu;
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
  start(attempt: string, stage: StageName, key: string | null): void {
    if (this.file) appendFileSync(this.file, JSON.stringify({ event: "start", attempt, stage, key }) + "\n");
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

/** A JSON value with object keys sorted, arrays in their order: the
 * canonical encoding keys are digests of. */
export type Canonical = null | boolean | number | string | readonly Canonical[] | { readonly [key: string]: Canonical };
const isCanonicalList = (value: Canonical): value is readonly Canonical[] => Array.isArray(value);
export function canonical(value: Canonical): string {
  if (value === null || typeof value !== "object") return JSON.stringify(value);
  if (isCanonicalList(value)) return `[${value.map(canonical).join(",")}]`;
  const record: { readonly [key: string]: Canonical } = value;
  return `{${Object.keys(record).sort().map((k) => `${JSON.stringify(k)}:${canonical(record[k])}`).join(",")}}`;
}
export const sha256 = (bytes: string | Buffer): string => createHash("sha256").update(bytes).digest("hex");

// ---------------------------------------------------------------------------
// Implementation identity

/** A file's digest, memoized within the process by its status (device,
 * inode, size, modification and change times): a file rewritten in place
 * changes its change time. */
const digests = new Map<string, { signature: string; digest: string }>();
function fileDigest(path: string): string {
  const s = statSync(path, { bigint: true });
  const signature = `${s.dev}:${s.ino}:${s.size}:${s.mtimeNs}:${s.ctimeNs}`;
  const known = digests.get(path);
  if (known?.signature === signature) return known.digest;
  const digest = sha256(readFileSync(path));
  digests.set(path, { signature, digest });
  return digest;
}

/** The repository modules `file` imports by a relative specifier, itself
 * first, transitively: the code an adapter's digest covers. */
function moduleClosure(file: string): string[] {
  const seen: string[] = [];
  for (let work = [file], next = work.shift(); next !== undefined; next = work.shift()) {
    if (seen.includes(next)) continue;
    seen.push(next);
    const text = readFileSync(next, "utf8");
    for (const m of text.matchAll(/(?:from|import)\s+"(\.\.?\/[^"]+\.m?ts)"/g))
      work.push(resolve(dirname(next), m[1]));
  }
  return seen;
}
/** The digest of modules' sources, transitively, by their repository paths. */
const closureDigests = new Map<string, Canonical>();
export function codeIdentity(files: readonly string[]): Canonical {
  const key = files.join("\n");
  const known = closureDigests.get(key);
  if (known !== undefined) return known;
  const repository = resolve(here, "..");
  const all = [...new Set(files.flatMap(moduleClosure))].sort();
  const identity = all.map((f) => [f.startsWith(repository + "/") ? f.slice(repository.length + 1) : f, fileDigest(f)]);
  closureDigests.set(key, identity);
  return identity;
}

/** The operating system's build, which identifies the libraries of its sealed
 * system volume (`/usr/lib`, `/System`) on macOS; null elsewhere. */
let systemBuild: string | null | undefined;
function osBuild(): string | null {
  if (systemBuild !== undefined) return systemBuild;
  systemBuild = null;
  if (platform() === "darwin") {
    const plist = readFileSync("/System/Library/CoreServices/SystemVersion.plist", "utf8");
    const at = /<key>ProductBuildVersion<\/key>\s*<string>([^<]+)<\/string>/.exec(plist);
    systemBuild = at?.[1] ?? null;
  }
  return systemBuild;
}
const systemPrefixes = ["/usr/lib/", "/System/"];

/** The dynamic libraries an executable links, each by its digest or, on the
 * sealed system volume, by the system's build; or why they are not
 * identified. */
const libraries = new Map<string, Canonical | string>();
function linkedLibraries(executable: string, digest: string): Canonical | string {
  const known = libraries.get(digest);
  if (known !== undefined) return known;
  let found: Canonical | string;
  const build = osBuild();
  if (platform() !== "darwin" || build === null) found = "dynamic libraries are identified on macOS only";
  else {
    const listed = spawnSync("/usr/bin/otool", ["-L", executable], { encoding: "utf8", env: {} });
    if (listed.status !== 0) found = `otool -L failed: ${listed.stderr.trim().split("\n")[0] ?? ""}`;
    else {
      const paths = listed.stdout.split("\n").slice(1).map((l) => l.trim().split(" (")[0]).filter((p) => p !== "");
      const unidentified = paths.find((p) => !systemPrefixes.some((s) => p.startsWith(s)));
      found = unidentified !== undefined
        ? `a library outside the system volume: ${unidentified}`
        : paths.map((p) => [p, `system ${build}`]);
    }
  }
  libraries.set(digest, found);
  return found;
}

/** The identity of an audited program's executable: its digest, its linked
 * libraries and the platform it runs on; or why it has none. Only the
 * repository's builds of the verifier and the producer are audited: their
 * I/O is the files their arguments name, standard output and standard error;
 * they start no process and read no environment variable the invocation
 * does not fix (the Lean runtime's and OCaml's are unset). Any other program
 * (a test's stand-in, the mutation verifier) has dependencies that are not
 * identified. */
function executableIdentity(program: string): { identity: Canonical } | { unidentified: string } {
  let real: string;
  try {
    real = realpathSync(program);
  } catch {
    return { unidentified: `${program} does not resolve` };
  }
  const audited = [verifierBuild, producerBuild].some((b) => {
    try {
      return realpathSync(b) === real;
    } catch {
      return false;
    }
  });
  if (!audited) return { unidentified: `${basename(program)} is not the repository's build of an audited program` };
  const digest = fileDigest(real);
  const linked = linkedLibraries(real, digest);
  if (typeof linked === "string") return { unidentified: linked };
  return { identity: { executable: digest, libraries: linked, platform: platform(), arch: arch() } };
}

// ---------------------------------------------------------------------------
// Process stages

/** One argument of a process stage: literal text, an input file bound by
 * content under the name of its role, or an output file the stage writes
 * under the name of its role and the caller receives at `path`. */
export type Argument = { text: string } | { input: string; path: string } | { output: string; path: string };

/** A stage's exit protocol: success is status 0; a refusal is `status` with
 * a record whose first line starts with `prefix` and whose last line is
 * `end of refusal`. Anything else is an operational failure. */
export type Protocol = { refusal: { status: number; prefix: string } | null };

/** The line that ends a refusal record. */
export const refusalEnd = "end of refusal";

export type ProcessCall = {
  stage: StageName;
  program: string;
  arguments: readonly Argument[];
  /** The child's whole environment. */
  environment: Readonly<Record<string, string>>;
  protocol: Protocol;
};

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

/** The largest output a stage may print. */
const maxBuffer = 16 * 1024 * 1024;
const text = (bytes: Buffer): string => new TextDecoder("utf-8").decode(bytes);

/** Whether a stage's exit is a finished result under its protocol. */
export function finishedExit(protocol: Protocol, status: number | null, stdout: string, stderr: string): boolean {
  if (status === 0) return true;
  const detail = stderr.trim() || stdout.trim();
  const lines = detail.split("\n");
  return protocol.refusal !== null && status === protocol.refusal.status &&
    detail.startsWith(protocol.refusal.prefix) && lines.at(-1) === refusalEnd;
}

/** Run a process stage: its inputs copied by content into a fresh execution
 * directory under their roles' names, the program run there with relative
 * arguments and the call's environment, its outputs copied to the caller's
 * paths. */
export function invokeProcess(call: ProcessCall, options: InvokeOptions): Invoked {
  const attempt = randomUUID();
  const started = performance.now();
  const forced = options.force || storeSetting().off;
  const directory = runDirectory(`stage-${call.stage}-`);
  try {
    const argv: string[] = [];
    const inputs: Canonical[] = [];
    const outputs: { role: string; path: string }[] = [];
    const roles = new Set<string>();
    for (const a of call.arguments) {
      if ("text" in a) {
        argv.push(a.text);
        continue;
      }
      const role = "input" in a ? a.input : a.output;
      if (roles.has(role) || role !== basename(role)) throw Error(`stage ${call.stage}: role ${role} is not one file name`);
      roles.add(role);
      argv.push(role);
      if ("output" in a) {
        outputs.push({ role, path: a.path });
        continue;
      }
      const bytes = readOrAbsent(a.path);
      if (bytes !== null) writeFileSync(join(directory, role), bytes);
      inputs.push([role, bytes === null ? null : sha256(bytes)]);
    }
    const implementation = executableIdentity(call.program);
    const manifest: Canonical = {
      stage: call.stage,
      adapter: codeIdentity([import.meta.filename]),
      implementation: "identity" in implementation ? implementation.identity : null,
      argv,
      environment: call.environment,
      inputs,
      outputs: outputs.map((o) => o.role),
    };
    const key = "identity" in implementation ? sha256(canonical(manifest)) : null;
    const ineligible = "unidentified" in implementation ? implementation.unidentified : null;
    options.recorder?.start(attempt, call.stage, key);
    const p = spawnSync(call.program, argv, {
      cwd: directory,
      env: { ...call.environment },
      timeout: options.limitMs,
      maxBuffer,
    });
    const stdoutBytes = p.stdout ? Buffer.from(p.stdout) : Buffer.alloc(0);
    const stderrBytes = p.stderr ? Buffer.from(p.stderr) : Buffer.alloc(0);
    const stdout = text(stdoutBytes), stderr = text(stderrBytes);
    const timedOut = (p.error && "code" in p.error && p.error.code === "ETIMEDOUT") ?? false;
    const execution: Execution = timedOut ? "timed-out"
      : p.error || p.signal || p.status === null || !finishedExit(call.protocol, p.status, stdout, stderr) ? "failed"
      : "executed";
    for (const o of outputs) {
      const bytes = readOrAbsent(join(directory, o.role));
      if (bytes !== null) writeFileSync(o.path, bytes);
    }
    const record: AttemptRecord = {
      attempt, stage: call.stage, key, ineligible, forced, limitMs: options.limitMs, execution,
      exitStatus: p.status, elapsedMs: performance.now() - started,
      cpu: { unavailable: "the child process's CPU time is not measured" },
    };
    options.recorder?.finish(record);
    return { status: p.status, signal: p.signal, error: p.error, stdoutBytes, stderrBytes, stdout, stderr, record };
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

/** A file's bytes, or null where its path names nothing. */
function readOrAbsent(path: string): Buffer | null {
  try {
    return readFileSync(path);
  } catch (error) {
    if (error instanceof Error && "code" in error && (error.code === "ENOENT" || error.code === "ENOTDIR")) return null;
    throw error;
  }
}

/** The verifier's refusal and the producer's. */
const verifierProtocol: Protocol = { refusal: { status: 1, prefix: "reject: " } };
const producerProtocol: Protocol = { refusal: { status: 2, prefix: "unsupported: " } };

/** A verifier invocation, its command line read by its modes:
 * `[--subtype-rounds n] --lower-control-flow <fragment>`,
 * `… --produce-source-claims <fragment> <claims> <file-key> <evidence-out> <depth>`,
 * `… --check-source-claims <fragment> <claims> <file-key> <evidence>`. */
export function verifierCall(program: string, args: readonly string[],
    environment: Readonly<Record<string, string>> = {}): ProcessCall {
  const budget = args[0] === "--subtype-rounds" ? args.slice(0, 2).map((t) => ({ text: t })) : [];
  const [mode, ...rest] = args.slice(budget.length);
  const call = (stage: StageName, list: Argument[]): ProcessCall =>
    ({ stage, program, arguments: [...budget, { text: mode }, ...list], environment, protocol: verifierProtocol });
  if (mode === "--lower-control-flow" && rest.length === 1)
    return call("lower", [{ input: "fragment.json", path: rest[0] }]);
  if (mode === "--produce-source-claims" && rest.length === 5)
    return call("search", [{ input: "fragment.json", path: rest[0] }, { input: "claims.json", path: rest[1] },
      { text: rest[2] }, { output: "evidence.json", path: rest[3] }, { text: rest[4] }]);
  if (mode === "--check-source-claims" && rest.length === 4)
    return call("check", [{ input: "fragment.json", path: rest[0] }, { input: "claims.json", path: rest[1] },
      { text: rest[2] }, { input: "evidence.json", path: rest[3] }]);
  throw Error(`not a verifier stage: ${args.join(" ")}`);
}

/** A producer invocation: `<fragment> <flow> [<qualified reads>]` proposes,
 * `--explain <fragment> <flow>` explains. */
export function producerCall(program: string, args: readonly string[]): ProcessCall {
  const documents = (list: readonly string[]): Argument[] =>
    list.map((path, i) => ({ input: ["fragment.json", "flow.json", "qualified.json"][i], path }));
  if (args[0] === "--explain" && args.length === 3)
    return { stage: "explain", program, arguments: [{ text: "--explain" }, ...documents(args.slice(1))],
      environment: {}, protocol: { refusal: null } };
  if (args.length === 2 || args.length === 3)
    return { stage: "propose", program, arguments: documents(args), environment: {}, protocol: producerProtocol };
  throw Error(`not a producer stage: ${args.join(" ")}`);
}

/** Whether an attempt ran its stage: executed, timed out or failed, not
 * replayed. */
export const ran = (record: AttemptRecord): boolean =>
  record.execution === "executed" || record.execution === "timed-out" || record.execution === "failed";

/** A control's run of the operation it tests: forced, and required to have
 * executed. */
export function forced(call: ProcessCall, limitMs: number = 30_000): Invoked {
  const invoked = invokeProcess(call, { limitMs, force: true, recorder: null });
  if (!ran(invoked.record)) throw Error(`control: ${call.stage} was not executed (${invoked.record.execution})`);
  return invoked;
}

// ---------------------------------------------------------------------------
// In-process stages

/** A stage computed in this process: its known inputs by role, and its run. */
export type InProcessCall<T> = {
  stage: StageName;
  /** The modules implementing the stage, whose sources identify it; or why
   * its dependencies are not identified. */
  implementation: { modules: readonly string[] } | { unidentified: string };
  inputs: readonly { role: string; bytes: string | Buffer }[];
  run: () => T;
};

/** Run an in-process stage, recording its attempt: an exception it throws is
 * an operational failure, recorded and thrown on. */
export function invokeInProcess<T>(call: InProcessCall<T>, options: { force: boolean; recorder: Recorder | null }):
    { value: T; record: AttemptRecord } {
  const attempt = randomUUID();
  const started = performance.now();
  const cpu = process.cpuUsage();
  const forced = options.force || storeSetting().off;
  const manifest: Canonical = {
    stage: call.stage,
    implementation: "modules" in call.implementation
      ? { code: codeIdentity(call.implementation.modules), node: process.version, platform: platform(), arch: arch() }
      : null,
    inputs: call.inputs.map((i) => [i.role, sha256(i.bytes)]),
  };
  const key = "modules" in call.implementation ? sha256(canonical(manifest)) : null;
  const ineligible = "unidentified" in call.implementation ? call.implementation.unidentified : null;
  options.recorder?.start(attempt, call.stage, key);
  const record = (execution: Execution): AttemptRecord => {
    const used = process.cpuUsage(cpu);
    return {
      attempt, stage: call.stage, key, ineligible, forced, limitMs: null, execution, exitStatus: null,
      elapsedMs: performance.now() - started,
      cpu: { userMs: used.user / 1000, systemMs: used.system / 1000, covers: "the pipeline's process" },
    };
  };
  let value: T;
  try {
    value = call.run();
  } catch (error) {
    options.recorder?.finish(record("failed"));
    throw error;
  }
  const done = record("executed");
  options.recorder?.finish(done);
  return { value, record: done };
}

// ---------------------------------------------------------------------------
// Records read back

/** An invocation record a run wrote, read field by field. */
export function readAttemptRecord(value: unknown): AttemptRecord {
  const fail = (): never => {
    throw Error(`not an attempt record: ${JSON.stringify(value)?.slice(0, 200)}`);
  };
  if (typeof value !== "object" || value === null) return fail();
  const v: { [key: string]: unknown } = { ...value };
  const nullableString = (x: unknown): x is string | null => x === null || typeof x === "string";
  const nullableNumber = (x: unknown): x is number | null => x === null || typeof x === "number";
  const { attempt, stage, key, ineligible, forced, limitMs, execution, exitStatus, elapsedMs, cpu } = v;
  if (typeof attempt !== "string" || !isStageName(stage) || !nullableString(key) || !nullableString(ineligible) ||
      typeof forced !== "boolean" || !nullableNumber(limitMs) || !executions.some((e) => e === execution) ||
      !nullableNumber(exitStatus) || typeof elapsedMs !== "number" || typeof cpu !== "object" || cpu === null)
    return fail();
  const c: { [key: string]: unknown } = { ...cpu };
  const readCpu: Cpu = typeof c["unavailable"] === "string" ? { unavailable: c["unavailable"] }
    : typeof c["userMs"] === "number" && typeof c["systemMs"] === "number" && typeof c["covers"] === "string"
      ? { userMs: c["userMs"], systemMs: c["systemMs"], covers: c["covers"] }
      : fail();
  const found = executions.find((e) => e === execution) ?? fail();
  return { attempt, stage, key, ineligible, forced, limitMs, execution: found, exitStatus, elapsedMs, cpu: readCpu };
}

/** The attempts of a run's invocation log (`Recorder`), in order; an attempt
 * started and never recorded is `interrupted`. */
export function readInvocationLog(file: string): AttemptRecord[] {
  const bytes = readOrAbsent(file);
  if (bytes === null) return [];
  const records: AttemptRecord[] = [];
  const open = new Map<string, { stage: StageName; key: string | null; at: number }>();
  for (const line of bytes.toString("utf8").split("\n")) {
    if (line === "") continue;
    const event: unknown = JSON.parse(line);
    if (typeof event !== "object" || event === null) throw Error(`not an invocation event: ${line.slice(0, 200)}`);
    const e: { [key: string]: unknown } = { ...event };
    if (e["event"] === "start" && typeof e["attempt"] === "string" && isStageName(e["stage"]) &&
        (e["key"] === null || typeof e["key"] === "string")) {
      open.set(e["attempt"], { stage: e["stage"], key: e["key"], at: records.length });
      records.push({ attempt: e["attempt"], stage: e["stage"], key: e["key"], ineligible: null, forced: false,
        limitMs: null, execution: "interrupted", exitStatus: null, elapsedMs: 0,
        cpu: { unavailable: "the attempt was interrupted" } });
    } else if (e["event"] === "end") {
      const record = readAttemptRecord(e["record"]);
      const started = open.get(record.attempt);
      if (started) {
        records[started.at] = record;
        open.delete(record.attempt);
      } else records.push(record);
    } else throw Error(`not an invocation event: ${line.slice(0, 200)}`);
  }
  return records;
}
