// The common invocation mechanism of the pipeline's stages (DESIGN.md, "The
// stage store"). Every stage of `verify-source.mts` and every control of the
// suites runs through `invokeProcess` or `invokeInProcess`: an invocation
// binds its input files by content into a fresh execution directory, runs
// with a fixed argument vector and environment, and records its attempt
// (its input description, timing, limit, outcome and, where its
// dependencies are identified, its complete stage key). A replay-eligible
// invocation of a replayed stage is looked up in the store
// (`stage-store.mts`) by its key, and its finished result or timeout is
// published there.
//   node pipeline/stages.mts clean    removes entries and timeout observations
import { spawnSync } from "node:child_process";
import { createHash, randomUUID } from "node:crypto";
import { appendFileSync, readFileSync, realpathSync, rmSync, statSync, writeFileSync } from "node:fs";
import { arch, homedir, platform } from "node:os";
import { basename, dirname, join, resolve } from "node:path";
import { runDirectory } from "./run-directory.mts";
import { readMeasurement, Store, type Cpu, type Measurement, type StoredResult } from "./stage-store.mts";
import { isOperation, observationsHold, observed, type Observation } from "../tools/files.mts";
import { compilerImplementation } from "../tools/compiler-channel.mts";

export type { Cpu, Measurement } from "./stage-store.mts";

const here = import.meta.dirname;

/** The stages of the pipeline's entry point (DESIGN.md, "The stage store"). */
export type StageName = "parse" | "lower" | "propose" | "assemble" | "search" | "check" | "explain" | "diagnostics";
const stageNames: readonly StageName[] = ["parse", "lower", "propose", "assemble", "search", "check", "explain",
  "diagnostics"];
export const isStageName = (value: unknown): value is StageName => stageNames.some((s) => s === value);

/** The stages that replay: every stage. A replayed check is the verifier's
 * result for exactly its key's inputs: the verifier's check mode reads the
 * three files its arguments name and prints its judgment, and reads no clock,
 * randomness, environment or working directory (DESIGN.md, the trust
 * surface). The parse and TypeScript's diagnostics are observed stages, keyed
 * by the file system's answers to their reads (DESIGN.md, "Observed
 * stages"). */
const replayedStages: ReadonlySet<StageName> = new Set<StageName>(stageNames);

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
const digests = new Map<string, { signature: string; digest: string; imports: string[] | null }>();
function known(path: string): { signature: string; digest: string; imports: string[] | null } {
  const s = statSync(path, { bigint: true });
  const signature = `${s.dev}:${s.ino}:${s.size}:${s.mtimeNs}:${s.ctimeNs}`;
  const held = digests.get(path);
  if (held?.signature === signature) return held;
  const fresh = { signature, digest: sha256(readFileSync(path)), imports: null };
  digests.set(path, fresh);
  return fresh;
}
const fileDigest = (path: string): string => known(path).digest;

/** The modules `file` imports by a relative specifier, read from its text,
 * kept with its digest where the text read is the one digested. */
function relativeImports(file: string): string[] {
  const held = known(file);
  if (held.imports) return held.imports;
  const bytes = readFileSync(file);
  const imports = [...bytes.toString("utf8").matchAll(/(?:from|import)\s+"(\.\.?\/[^"]+\.m?ts)"/g)]
    .map((m) => resolve(dirname(file), m[1]));
  if (sha256(bytes) === held.digest) held.imports = imports;
  return imports;
}

/** The repository modules `file` imports by a relative specifier, itself
 * first, transitively: the code an adapter's digest covers. */
function moduleClosure(file: string): string[] {
  const seen: string[] = [];
  for (let work = [file], next = work.shift(); next !== undefined; next = work.shift()) {
    if (seen.includes(next)) continue;
    seen.push(next);
    work.push(...relativeImports(next));
  }
  return seen;
}
/** The digests of modules' sources, transitively, by their repository paths. */
export function codeIdentity(files: readonly string[]): Canonical {
  const repository = resolve(here, "..");
  const all = [...new Set(files.flatMap(moduleClosure))].sort();
  return all.map((f) => [f.startsWith(repository + "/") ? f.slice(repository.length + 1) : f, fileDigest(f)]);
}

/** A module closure captured during module evaluation. Callers retain this
 * identity with the implementation they loaded. */
export type LoadedCode = { identity: Canonical; changed: () => boolean };
export function captureCodeIdentity(files: readonly string[]): LoadedCode {
  const identity = codeIdentity(files);
  const encoded = canonical(identity);
  return { identity, changed: (): boolean => {
    try {
      return canonical(codeIdentity(files)) !== encoded;
    } catch {
      return true;
    }
  } };
}
const adapter = captureCodeIdentity([import.meta.filename]);

/** The operating system's build, which identifies the files of its sealed
 * system volume on macOS; null elsewhere. */
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
/** The directories of macOS's sealed system volume. */
const systemPrefixes = ["/usr/lib/", "/System/", "/bin/", "/usr/bin/"];
const onSystemVolume = (path: string): boolean => systemPrefixes.some((s) => path.startsWith(s));

/** The dynamic libraries an executable links, transitively: each outside
 * the system volume by its digest, each on it by the system's build; or why
 * they are not identified. */
export function linkedLibraries(executable: string): Canonical | string {
  return identifyLibraries(executable);
}
function identifyLibraries(executable: string, files?: Map<string, string>): Canonical | string {
  const build = osBuild();
  let found: Canonical | string;
  if (platform() !== "darwin" || build === null) found = "dynamic libraries are identified on macOS only";
  else {
    const identified: Canonical[] = [];
    found = identified;
    const seen = new Set<string>();
    // Each file to list: its real path and its digest.
    const start = realpathSync(executable);
    files?.set(executable, canonical([start, fileDigest(start)]));
    for (let work = [{ real: start, digest: fileDigest(start) }], item = work.shift(); item !== undefined;
        item = work.shift()) {
      const next = item.real;
      const listed = otool("-L", next, item.digest);
      if (listed.status !== 0) {
        found = `otool -L ${next} failed: ${listed.stderr.trim().split("\n")[0] ?? ""}`;
        break;
      }
      const named = listed.stdout.split("\n").slice(1).map((l) => l.trim().split(" (")[0]).filter((p) => p !== "");
      // A name relative to the loader or its run paths is resolved as dyld
      // resolves it: `@loader_path` by the loading file's directory,
      // `@executable_path` by the executable's, `@rpath` by the first run
      // path of the loader or the executable naming an existing file.
      const paths: string[] = [];
      for (const p of named) {
        const resolved = p.startsWith("@") ? resolveLoaderName(p, next, executable) : p;
        if (resolved === null) {
          found = `a library dyld's rules do not resolve here: ${p} (from ${next})`;
          break;
        }
        paths.push(resolved);
      }
      if (typeof found === "string") break;
      for (const p of paths) {
        if (seen.has(p)) continue;
        seen.add(p);
        if (onSystemVolume(p)) identified.push([p, `system ${build}`]);
        else {
          const real = realpathSync(p);
          const digest = fileDigest(real);
          if (!files?.has(p)) files?.set(p, canonical([real, digest]));
          identified.push([p, digest]);
          work.push({ real, digest });
        }
      }
    }
  }
  return found;
}

/** Resolve the developer-tool shim before memoizing listings. Bootstrap the
 * tool's own dependency identity with fresh listings from that same tool. */
let listingTool: string | undefined;
let listingIdentity: Canonical | undefined;
const listingFiles = new Map<string, string>();
let identifyingListingTool: boolean = false;
const listings = new Map<string, { status: number | null; stdout: string; stderr: string }>();
/** Recheck the bootstrap's paths and contents through the stat-memoized digests. */
function listingToolUnchanged(): boolean {
  try {
    for (const [path, identity] of listingFiles) {
      const real = realpathSync(path);
      if (canonical([real, fileDigest(real)]) !== identity) return false;
    }
    return true;
  } catch {
    return false;
  }
}
function otool(flag: "-L" | "-l", file: string, digest: string = fileDigest(realpathSync(file))):
    { status: number | null; stdout: string; stderr: string } {
  if (listingTool === undefined) {
    const selected = spawnSync("/usr/bin/xcrun", ["--find", "otool"], { encoding: "utf8", env: {} });
    listingTool = selected.status === 0 ? selected.stdout.trim() : "/usr/bin/otool";
    identifyingListingTool = true;
    try {
      const libraries = identifyLibraries(listingTool, listingFiles);
      if (selected.status === 0 && typeof libraries !== "string" && listingToolUnchanged())
        listingIdentity = [realpathSync(listingTool), fileDigest(realpathSync(listingTool)), libraries, osBuild()];
    } finally {
      identifyingListingTool = false;
    }
  }
  const fresh = (): { status: number | null; stdout: string; stderr: string } => {
    const listed = spawnSync(listingTool ?? "/usr/bin/otool", [flag, file], { encoding: "utf8", env: {} });
    return { status: listed.status, stdout: listed.stdout ?? "", stderr: listed.stderr ?? String(listed.error ?? "") };
  };
  if (identifyingListingTool || listingIdentity === undefined) return fresh();
  const changed = { status: 1, stdout: "", stderr: "otool or its dependencies differ from their identified contents" };
  if (!listingToolUnchanged()) return changed;
  const key = sha256(canonical(["otool", listingIdentity, flag, digest]));
  const held = listings.get(key);
  if (held) return held;
  const store = currentStore();
  const stored = store?.memo("otool", key) ?? null;
  if (!listingToolUnchanged()) return changed;
  const result = stored === null ? fresh() : { status: 0, stdout: stored, stderr: "" };
  if (!listingToolUnchanged()) return changed;
  if (stored === null && result.status === 0) store?.publishMemo("otool", key, result.stdout);
  listings.set(key, result);
  return result;
}

/** The run paths a Mach-O file declares (`LC_RPATH`). */
function runPaths(file: string): string[] {
  const listed = otool("-l", file);
  if (listed.status !== 0) return [];
  return [...listed.stdout.matchAll(/cmd LC_RPATH\s+cmdsize \d+\s+path (.+?) \(offset \d+\)/g)].map((m) => m[1]);
}
/** A library name relative to its loader, resolved, or null. */
function resolveLoaderName(name: string, loader: string, executable: string): string | null {
  const expand = (path: string): string => path.replace(/^@loader_path/, dirname(loader))
    .replace(/^@executable_path/, dirname(executable));
  const exists = (path: string): boolean => {
    try {
      statSync(path);
      return true;
    } catch {
      return false;
    }
  };
  if (name.startsWith("@loader_path/") || name.startsWith("@executable_path/")) {
    const path = resolve(expand(name));
    return exists(path) ? path : null;
  }
  if (!name.startsWith("@rpath/")) return null;
  const rest = name.slice("@rpath/".length);
  for (const base of [...runPaths(loader), ...(loader === executable ? [] : runPaths(executable))]) {
    const path = resolve(expand(base), rest);
    if (exists(path)) return path;
  }
  return null;
}

/** The programs whose I/O is audited, beside the repository's builds: a
 * test's stand-ins, each with the files it reads or runs. */
const auditedForTests = new Map<string, readonly string[]>();
/** Treat `program` as audited, its only dependencies itself, its
 * interpreter and `dependencies`: for the store's tests, whose stand-in
 * stages are shell scripts. */
export function auditForTests(program: string, dependencies: readonly string[]): void {
  auditedForTests.set(realpathSync(program), dependencies);
}

/** The identity of an audited program's executable: its digest, its linked
 * libraries and the platform it runs on; or why it has none. Only the
 * repository's builds of the verifier and the producer are audited: their
 * I/O is the files their arguments name, standard output and standard error;
 * they start no process, do not read their working directory's path, and
 * read no environment variable the invocation does not fix (the Lean
 * runtime's and OCaml's are unset). Any other program (a test's stand-in,
 * the mutation verifier) has dependencies that are not identified. */
function executableIdentity(program: string, environment: Readonly<Record<string, string>>):
    { identity: Canonical } | { unidentified: string } {
  if (Object.keys(environment).some((name) => name.startsWith("DYLD_")))
    return { unidentified: "child DYLD_ environment variables have unidentified code dependencies" };
  let real: string;
  try {
    real = realpathSync(program);
  } catch {
    return { unidentified: `${program} does not resolve` };
  }
  const builds = [verifierBuild, producerBuild].some((b) => {
    try {
      return realpathSync(b) === real;
    } catch {
      return false;
    }
  });
  const declared = auditedForTests.get(real);
  if (!builds && declared === undefined)
    return { unidentified: `${basename(program)} is not the repository's build of an audited program` };
  const files: Canonical[] = [];
  if (declared !== undefined) {
    // A script: itself, its interpreter and what it declares.
    const interpreter = /^#!(\S+)/.exec(readFileSync(real, "utf8"))?.[1];
    for (const dependency of [...(interpreter ? [interpreter] : []), ...declared]) {
      if (onSystemVolume(dependency) && osBuild() !== null) files.push([dependency, `system ${osBuild()}`]);
      else files.push([dependency, fileDigest(realpathSync(dependency))]);
    }
    return { identity: { executable: fileDigest(real), files, platform: platform(), arch: arch() } };
  }
  const linked = linkedLibraries(real);
  if (typeof linked === "string") return { unidentified: linked };
  return { identity: { executable: fileDigest(real), libraries: linked, platform: platform(), arch: arch() } };
}

/** The Node runtime the adapters run on: its executable and linked
 * libraries by content, its options (`execArgv`, `NODE_OPTIONS`); or why it
 * is not identified. */
function diskNodeIdentity(): { identity: Canonical } | { unidentified: string } {
  if (Object.keys(process.env).some((name) => name.startsWith("DYLD_")))
    return { unidentified: "Node DYLD_ environment variables have unidentified code dependencies" };
  const options = [...process.execArgv, process.env["NODE_OPTIONS"] ?? ""].join(" ");
  if (/(?:^|[\s"'])(?:--(?:import|require|loader|experimental[-_]loader)(?:[=\s"']|$)|-r)/.test(options))
    return { unidentified: "Node import, require or loader options have unidentified code dependencies" };
  const real = realpathSync(process.execPath);
  const linked = linkedLibraries(real);
  if (typeof linked === "string") return { unidentified: `Node: ${linked}` };
  return { identity: { executable: fileDigest(real), libraries: linked, options: [...process.execArgv],
    nodeOptions: process.env["NODE_OPTIONS"] ?? null, platform: platform(), arch: arch() } };
}

/** The runtime identity captured with the adapter's loaded code. */
const loadedRuntime = diskNodeIdentity();
function nodeIdentity(): { identity: Canonical } | { unidentified: string } {
  if ("unidentified" in loadedRuntime) return loadedRuntime;
  try {
    if (canonical(diskNodeIdentity()) === canonical(loadedRuntime)) return loadedRuntime;
  } catch {
    // A missing or unreadable runtime dependency cannot authorize replay.
  }
  return { unidentified: "loaded Node runtime differs from disk" };
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
/** What, beside the limit, decides whether a process stage times out. */
const resourcePolicy = canonical({ maxBuffer, killSignal: "SIGTERM", spawn: "spawnSync" });
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
 * paths. A replay-eligible invocation of a replayed stage, not forced,
 * replays a finished result stored at its key, or reports a timeout
 * observed there at a limit no smaller than its own; executed, its finished
 * result or its timeout is published. */
export function invokeProcess(call: ProcessCall, options: InvokeOptions): Invoked {
  if (!Number.isSafeInteger(options.limitMs) || options.limitMs <= 0)
    throw Error("a process stage limit must be a positive integer number of milliseconds");
  // The program as the caller's working directory names it.
  const program = resolve(call.program);
  const attempt = randomUUID();
  const started = performance.now();
  const startedAt = Date.now();
  const store = currentStore();
  const forced = options.force || store === null;
  const directory = runDirectory(`stage-${call.stage}-`);
  try {
    const argv: string[] = [];
    const inputs: Canonical[] = [];
    const inputFiles: [string, Buffer][] = [];
    const outputs: { role: string; path: string }[] = [];
    const roles = new Set<string>();
    const inputRoles = new Map<string, string>();
    for (const a of call.arguments) if ("input" in a) inputRoles.set(resolve(a.path), a.input);
    for (const a of call.arguments) {
      if ("text" in a) {
        argv.push(a.text);
        continue;
      }
      const role = "input" in a ? a.input : a.output;
      if (roles.has(role) || role !== basename(role)) throw Error(`stage ${call.stage}: role ${role} is not one file name`);
      roles.add(role);
      if ("output" in a) {
        // An output at an input's path names that input, as the caller's
        // arguments do: the program sees the alias, and a refusal leaves the
        // caller's input intact.
        const alias = inputRoles.get(resolve(a.path));
        argv.push(alias ?? role);
        if (alias === undefined) outputs.push({ role, path: a.path });
        continue;
      }
      argv.push(role);
      const bytes = readOrAbsent(a.path);
      if (bytes !== null) inputFiles.push([role, bytes]);
      inputs.push([role, bytes === null ? null : sha256(bytes)]);
    }
    const implementation = executableIdentity(program, call.environment);
    const runtime = nodeIdentity();
    const manifest: Canonical = {
      stage: call.stage,
      adapter: adapter.identity,
      runtime: "identity" in runtime ? runtime.identity : null,
      implementation: "identity" in implementation ? implementation.identity : null,
      argv,
      environment: call.environment,
      inputs,
      outputs: outputs.map((o) => o.role),
    };
    const input = canonical(manifest);
    const ineligible = adapter.changed() ? "loaded adapter modules differ from disk"
      : "unidentified" in implementation ? implementation.unidentified
      : "unidentified" in runtime ? runtime.unidentified : null;
    const key = ineligible === null ? sha256(input) : null;
    const record = (execution: Execution, exitStatus: number | null, replay: Replay | null): AttemptRecord => ({
      attempt, stage: call.stage, key, ineligible, manifest, context: { program, directory }, forced,
      limitMs: options.limitMs, execution, exitStatus, elapsedMs: performance.now() - started,
      cpu: replay ? replay.stored.cpu : { unavailable: "the child process's CPU time is not measured" }, replay,
    });
    options.recorder?.start(record("interrupted", null, null), startedAt);
    const replaying = key !== null && store !== null && replayedStages.has(call.stage) ? { key, store } : null;
    if (replaying && !forced) {
      const found = replaying.store.finished(call.stage, replaying.key, input);
      if (found) {
        const materializing = performance.now();
        const produced = new Map(found.result.outputs);
        for (const o of outputs) {
          const bytes = produced.get(o.role);
          if (bytes !== undefined) writeFileSync(o.path, bytes);
        }
        const done = record("replayed", found.result.exitStatus, { lookupMs: found.lookupMs,
          validationMs: found.validationMs, materializationMs: performance.now() - materializing,
          stored: found.result.measurement });
        options.recorder?.finish(done);
        return { status: found.result.exitStatus, signal: null, error: undefined, stdoutBytes: found.result.stdout,
          stderrBytes: found.result.stderr, stdout: text(found.result.stdout), stderr: text(found.result.stderr),
          record: done };
      }
      const observed = replaying.store.timeout(call.stage, replaying.key, input, options.limitMs, resourcePolicy);
      if (observed) {
        const { observation } = observed;
        const done = record("timeout-replayed", null, { lookupMs: observed.lookupMs, validationMs: 0,
          materializationMs: 0, stored: { attempt: observation.attempt, elapsedMs: observation.elapsedMs,
            limitMs: observation.limitMs, cpu: { unavailable: "a timeout's CPU time is not measured" } } });
        options.recorder?.finish(done);
        return { status: null, signal: null, error: undefined, stdoutBytes: Buffer.alloc(0), stderrBytes: Buffer.alloc(0),
          stdout: "", stderr: "", record: done };
      }
    }
    // The inputs are bound into the execution directory by the bytes the key
    // digests, when the stage executes.
    for (const [role, bytes] of inputFiles) writeFileSync(join(directory, role), bytes);
    const p = spawnSync(program, argv, {
      cwd: directory,
      env: { ...call.environment },
      timeout: options.limitMs,
      maxBuffer,
    });
    const elapsedMs = performance.now() - started;
    const stdoutBytes = p.stdout ? Buffer.from(p.stdout) : Buffer.alloc(0);
    const stderrBytes = p.stderr ? Buffer.from(p.stderr) : Buffer.alloc(0);
    const stdout = text(stdoutBytes), stderr = text(stderrBytes);
    // A timeout is the expiry of this attempt's own enforced limit.
    const timedOut = (p.error && "code" in p.error && p.error.code === "ETIMEDOUT") ?? false;
    const finished = !p.error && !p.signal && p.status !== null && finishedExit(call.protocol, p.status, stdout, stderr);
    const execution: Execution = timedOut ? "timed-out" : finished ? "executed" : "failed";
    const produced: [string, Buffer][] = [];
    for (const o of outputs) {
      const bytes = readOrAbsent(join(directory, o.role));
      if (bytes === null) continue;
      produced.push([o.role, bytes]);
      writeFileSync(o.path, bytes);
    }
    const done = record(execution, p.status, null);
    if (replaying && execution === "executed")
      replaying.store.publishFinished(call.stage, replaying.key, { input, exitStatus: p.status, stdout: stdoutBytes,
        stderr: stderrBytes, outputs: produced, measurement: { attempt, elapsedMs, limitMs: options.limitMs,
          cpu: done.cpu } });
    if (replaying && execution === "timed-out")
      replaying.store.publishTimeout(call.stage, replaying.key, { input, attempt, elapsedMs, limitMs: options.limitMs,
        policy: resourcePolicy });
    options.recorder?.finish(done);
    return { status: p.status, signal: p.signal, error: p.error, stdoutBytes, stderrBytes, stdout, stderr, record: done };
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

/** This process's forced executions: their number and wall time, which a
 * suite reports as what its controls' tested operations cost. */
export const forcedExecutions: { count: number; elapsedMs: number } = { count: 0, elapsedMs: 0 };

/** A control's run of the operation it tests: forced, and required to have
 * executed. */
export function forced(call: ProcessCall, limitMs: number = 30_000): Invoked {
  const invoked = invokeProcess(call, { limitMs, force: true, recorder: null });
  forcedExecutions.count++;
  forcedExecutions.elapsedMs += invoked.record.elapsedMs;
  if (!ran(invoked.record)) throw Error(`control: ${call.stage} was not executed (${invoked.record.execution})`);
  return invoked;
}

// ---------------------------------------------------------------------------
// In-process stages

/** A stage computed in this process: its known inputs by role, and its run.
 * A replayed stage's value is text, the result its entry stores. */
export type InProcessCall<T> = {
  stage: StageName;
  /** The modules implementing the stage, whose sources identify it; or why
   * its dependencies are not identified. */
  implementation: LoadedCode | { unidentified: string };
  inputs: readonly { role: string; bytes: string | Buffer }[];
  run: () => T;
  /** The value as stored, and back: for a stage that replays. */
  codec?: { encode: (value: T) => Buffer; decode: (bytes: Buffer) => T };
  /** An observed stage (DESIGN.md, "Observed stages"): the file system's
   * answers to its reads are part of its key. */
  observed?: true;
};

/** An observed stage's manifest with its observations: the canonical text
 * a key is the digest of. */
const observedInput = (manifest: { readonly [key: string]: Canonical }, observations: readonly Observation[]): string =>
  canonical({ ...manifest, observations: observations.map(([operation, path, answer]) => [operation, path, answer]) });
/** The observations of a stored observed entry whose manifest is exactly
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

/** Run an in-process stage, recording its attempt: an exception it throws is
 * an operational failure, recorded and thrown on. A replay-eligible
 * invocation of a replayed stage with a codec replays and publishes as a
 * process stage does. An observed stage runs with its observations recorded,
 * replays a referenced entry whose observations hold now, and is published
 * where they are complete; where Node's caches disagree with the file system
 * it fails. */
export function invokeInProcess<T>(call: InProcessCall<T>, options: { force: boolean; recorder: Recorder | null }):
    { value: T; record: AttemptRecord } {
  const attempt = randomUUID();
  const started = performance.now();
  const startedAt = Date.now();
  const cpu = process.cpuUsage();
  const store = currentStore();
  const forced = options.force || store === null;
  const runtime = nodeIdentity();
  const compiler = call.observed ? compilerImplementation() : null;
  const manifest: { readonly [key: string]: Canonical } = {
    stage: call.stage,
    adapter: adapter.identity,
    runtime: "identity" in runtime ? runtime.identity : null,
    implementation: "identity" in call.implementation ? call.implementation.identity : null,
    inputs: call.inputs.map((i) => [i.role, sha256(i.bytes)]),
    ...(compiler ? { compiler: "identity" in compiler ? compiler.identity : null, system: osBuild() } : {}),
  };
  const input = canonical(manifest);
  const identityFailure = (): string | null => adapter.changed() ? "loaded adapter modules differ from disk"
    : "identity" in call.implementation && call.implementation.changed() ? "loaded implementation modules differ from disk"
    : "unidentified" in call.implementation ? call.implementation.unidentified
    : "unidentified" in runtime ? runtime.unidentified
    : compiler && "unobserved" in compiler ? compiler.unobserved
    : compiler && compiler.changed() ? "the loaded compiler differs from disk"
    : compiler && osBuild() === null ? "the system's build is not identified"
    : null;
  let ineligible = identityFailure();
  // An observed stage's manifest here is its pre-key's; its key is known
  // once its observations are.
  let key = ineligible === null ? sha256(input) : null;
  let recorded: Canonical = manifest;
  const record = (execution: Execution, replay: Replay | null): AttemptRecord => {
    const used = process.cpuUsage(cpu);
    return {
      attempt, stage: call.stage, key, ineligible, manifest: recorded, context: null, forced, limitMs: null, execution,
      exitStatus: null, elapsedMs: performance.now() - started,
      cpu: replay ? replay.stored.cpu : { userMs: used.user / 1000, systemMs: used.system / 1000,
        covers: "the pipeline's process" },
      replay,
    };
  };
  options.recorder?.start(record("interrupted", null), startedAt);
  const replaying = key !== null && store !== null && call.codec && replayedStages.has(call.stage)
    ? { key, store, codec: call.codec } : null;
  if (replaying && !forced) {
    const candidates = call.observed ? replaying.store.candidates(call.stage, replaying.key) : [replaying.key];
    for (const candidate of candidates) {
      const found = replaying.store.finished(call.stage, candidate, call.observed ? null : input);
      if (!found) continue;
      let validationMs = found.validationMs;
      if (call.observed) {
        const validating = performance.now();
        const observations = storedObservations(found.result.input, manifest);
        const holds = observations !== null && observationsHold(observations);
        validationMs += performance.now() - validating;
        if (!holds) continue;
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
  let value: T;
  let observations: Observation[] = [];
  try {
    if (call.observed) {
      const made = observed(call.run);
      if (made.inconsistent !== null)
        throw Error(`the process's caches may disagree with the file system (${made.inconsistent}); a fresh process is needed`);
      value = made.value;
      observations = made.observations;
      if (made.incomplete !== null) {
        ineligible ??= made.incomplete;
        key = null;
      }
    } else value = call.run();
  } catch (error) {
    options.recorder?.finish(record("failed", null));
    throw error;
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
    if (call.observed) replaying.store.reference(call.stage, replaying.key, key);
  }
  options.recorder?.finish(done);
  return { value, record: done };
}

/** A text value stored as its UTF-8 bytes. */
export const textCodec: { encode: (value: string) => Buffer; decode: (bytes: Buffer) => string } = {
  encode: (value: string): Buffer => Buffer.from(value, "utf8"),
  decode: (bytes: Buffer): string => bytes.toString("utf8"),
};

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

if (import.meta.filename === resolve(process.argv[1] ?? "") && process.argv[2] === "clean") {
  const store = currentStore();
  if (!store) {
    process.stderr.write("TSCERT_STAGE_STORE is off: there is no store to clean\n");
    process.exitCode = 2;
  } else {
    store.clean();
    process.stdout.write(`cleaned ${store.root}\n`);
  }
}
