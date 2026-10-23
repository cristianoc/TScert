// The execution adapter of process stages and the node side's code identity
// (DESIGN.md, "The stage store", keys). It describes an invocation
// (the stage, its argument vector, environment, exit protocol, input digests
// and output roles, with the identities of its executable and of the Node
// runtime), runs it in a fresh directory holding its inputs under their role
// names, classifies its exit, and delivers its outputs to the caller's paths.
// It identifies code by content: the node side's keyed files, an executable
// with its linked libraries, the runner the executable runs under, the
// runtime. The replay policy and the store
// (`stages.mts`, `stage-store.mts`) choose between running an invocation
// here and returning an entry whose stored description is its own.
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { closeSync, fstatSync, openSync, readdirSync, readFileSync, readSync, realpathSync, statSync, unlinkSync, writeFileSync }
  from "node:fs";
import { arch, constants, platform } from "node:os";
import { basename, dirname, join, resolve } from "node:path";
import { runDirectory } from "./run-directory.mts";
import type { Cpu } from "./stage-store.mts";

const here = import.meta.dirname;

/** The stages of the pipeline's entry point (DESIGN.md, "The stage store"). */
export type StageName = "parse" | "lower" | "propose" | "assemble" | "search" | "check" | "explain" | "diagnostics";
export const stageNames: readonly StageName[] = ["parse", "lower", "propose", "assemble", "search", "check", "explain",
  "diagnostics"];
export const isStageName = (value: unknown): value is StageName => stageNames.some((s) => s === value);

/** The repository's builds of the two audited programs, at their build
 * locations: the Lean verifier and the OCaml producer. */
export const verifierBuild: string = resolve(here, "../lean/.lake/build/bin/verifier");
export const producerBuild: string = resolve(here, "../ocaml-producer/_build/default/producer.exe");
/** The runner every process stage's program runs under
 * (`runner/stage-runner.c`, built by `make build-runner`), which reports the
 * CPU time of the stage's processes. */
export const runnerBuild: string = resolve(here, "runner/_build/stage-runner");

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
function known(path: string): { signature: string; digest: string } {
  const s = statSync(path, { bigint: true });
  const signature = `${s.dev}:${s.ino}:${s.size}:${s.mtimeNs}:${s.ctimeNs}`;
  const held = digests.get(path);
  if (held?.signature === signature) return held;
  const fresh = { signature, digest: sha256(readFileSync(path)) };
  digests.set(path, fresh);
  return fresh;
}
const fileDigest = (path: string): string => known(path).digest;

const repository = resolve(here, "..");

/** The files of the node side no key covers (DESIGN.md, "The stage store",
 * keys): each chooses among entries whose stored manifest is the
 * invocation's own, publishes or records attempts, orchestrates stages over
 * inputs their manifests bind, or presents outcomes. */
export const unkeyed: readonly string[] = [
  "pipeline/stages.mts", "pipeline/stage-store.mts", "pipeline/verify-source.mts", "pipeline/run-cases.mts",
  "pipeline/cases.mts", "pipeline/test.mts", "pipeline/default-parameters.mts", "pipeline/evidence-mutations.mts",
  "pipeline/generic-rest.mts", "pipeline/overload-claims.mts", "pipeline/rest-pack-instance.mts",
  "pipeline/run-example.mts", "pipeline/fixture-links.mts", "tools/diagnostic.mts", "tools/diagnostic-view.mts",
  "tools/claim-text.mts", "tools/unchecked.mts", "tools/shadow-contracts.mts", "tools/strip-types.mts",
  "tools/compiler-processes.mts",
];
/** The in-process stages' own modules, which no process stage executes. */
export const inProcessOnly: readonly string[] = [
  "pipeline/parse-stage.mts", "pipeline/claims-assembly.mts", "pipeline/in-process-execution.mts",
];

/** The digests, by sorted repository path, of the `.mts` files directly in
 * `directories` of `root` but `excluded`; or why they are not read. */
export function directoryIdentity(directories: readonly string[], excluded: readonly string[], root: string = repository):
    { identity: Canonical } | { unidentified: string } {
  try {
    const files = directories.flatMap((d) => readdirSync(join(root, d), { withFileTypes: true })
      .filter((e) => e.name.endsWith(".mts")).map((e) => {
        const path = `${d}/${e.name}`;
        if (!e.isFile()) throw Error(`${path} is no file`);
        return path;
      }))
      .filter((path) => !excluded.includes(path)).sort();
    return { identity: files.map((path) => [path, fileDigest(join(root, path))]) };
  } catch (error) {
    return { unidentified: `the node side's code is not read: ${error instanceof Error ? error.message : String(error)}` };
  }
}

/** A code identity captured when the process loads its modules, and whether
 * the file set or any content differs from disk now. */
export type LoadedCode = { identity: Canonical; changed: () => boolean };
function captureIdentity(directories: readonly string[], excluded: readonly string[]): LoadedCode | { unidentified: string } {
  const captured = directoryIdentity(directories, excluded);
  if ("unidentified" in captured) return captured;
  const encoded = canonical(captured.identity);
  return { identity: captured.identity, changed: (): boolean => {
    const now = directoryIdentity(directories, excluded);
    return !("identity" in now) || canonical(now.identity) !== encoded;
  } };
}

/** A process stage's code: the `.mts` files directly in `pipeline/` but the
 * unkeyed ones and the in-process stages' own. */
export const processCode: LoadedCode | { unidentified: string } =
  captureIdentity(["pipeline"], [...unkeyed, ...inProcessOnly]);
/** An in-process stage's code: the `.mts` files directly in `pipeline/` and
 * `tools/` but the unkeyed ones. */
export const inProcessCode: LoadedCode | { unidentified: string } = captureIdentity(["pipeline", "tools"], unkeyed);
/** Why a captured code identity gives no key now, or null. */
export const codeFailure = (code: LoadedCode | { unidentified: string }): string | null =>
  "unidentified" in code ? code.unidentified : code.changed() ? "loaded node-side modules differ from disk" : null;

/** The operating system's build, which identifies the files of its sealed
 * system volume on macOS; null elsewhere. */
let systemBuild: string | null | undefined;
export function osBuild(): string | null {
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
 * they are not identified. A file's libraries are the names its Mach-O load
 * commands state (`loadCommands`). */
export function linkedLibraries(executable: string): Canonical | string {
  const build = osBuild();
  if (platform() !== "darwin" || build === null) return "dynamic libraries are identified on macOS only";
  const identified: Canonical[] = [];
  const seen = new Set<string>();
  // Each file to read: the executable as named, then each library by its
  // real path; each with its digest.
  for (let work = [{ path: executable, digest: fileDigest(realpathSync(executable)) }], item = work.shift();
      item !== undefined; item = work.shift()) {
    const next = item.path;
    const commands = loadCommands(next, item.digest);
    if (typeof commands === "string") return `${next}: ${commands}`;
    // A name relative to the loader or its run paths is resolved as dyld
    // resolves it: `@loader_path` by the loading file's directory,
    // `@executable_path` by the executable's, `@rpath` by the first run
    // path of the loader or the executable naming an existing file.
    const paths: string[] = [];
    for (const p of commands.libraries) {
      const resolved = p.startsWith("@") ? resolveLoaderName(p, next, executable, commands.runPaths) : p;
      if (resolved === null) return `a library dyld's rules do not resolve here: ${p} (from ${next})`;
      paths.push(resolved);
    }
    for (const p of paths) {
      if (seen.has(p)) continue;
      seen.add(p);
      if (onSystemVolume(p)) identified.push([p, `system ${build}`]);
      else {
        const real = realpathSync(p);
        const digest = fileDigest(real);
        identified.push([p, digest]);
        work.push({ path: real, digest });
      }
    }
  }
  return identified;
}

/** The load commands of a Mach-O file that name libraries (its own install
 * name and every library it loads: required, weak, re-exported, lazy,
 * upward) and its run paths, in their order; or why the file is no Mach-O
 * file read here: one holding a command that names a library or changes
 * dyld's search otherwise (`LC_LAZY_LOAD_DYLIB_INFO`,
 * `LC_DYLD_ENVIRONMENT`), or a universal file whose architectures (those
 * its table counts, and an arm64 one described right after a 32-bit table)
 * differ in their libraries or run paths. Memoized by the file's digest
 * (`digest`), where the bytes read are the ones it names. */
type LoadCommands = { libraries: readonly string[]; runPaths: readonly string[] };
const loadCommandsOf = new Map<string, LoadCommands | string>();
const dylibCommands: ReadonlySet<number> = new Set([0xc, 0xd, 0x80000018, 0x8000001f, 0x20, 0x80000023]);
const runPathCommand = 0x8000001c;
const unreadCommands: ReadonlyMap<number, string> = new Map([[0x27, "LC_DYLD_ENVIRONMENT"], [0x3a, "LC_LAZY_LOAD_DYLIB_INFO"]]);
function loadCommands(file: string, digest: string): LoadCommands | string {
  const held = loadCommandsOf.get(digest);
  if (held !== undefined) return held;
  let found: LoadCommands | string;
  const descriptor = openSync(file, "r");
  try {
    const bytes = (offset: number, length: number): Buffer => {
      const buffer = Buffer.alloc(length);
      const read = readSync(descriptor, buffer, 0, length, offset);
      if (read !== length) throw Error(`the file ends at ${offset + read} before ${offset + length}`);
      return buffer;
    };
    // One architecture's image at `base`: a 32- or 64-bit little-endian header.
    const image = (base: number): LoadCommands => {
      const libraries: string[] = [], runPaths: string[] = [];
      const header = bytes(base, 28);
      const magic = header.readUInt32LE(0);
      if (magic !== 0xfeedface && magic !== 0xfeedfacf) throw Error(`no little-endian Mach-O header at ${base}`);
      const count = header.readUInt32LE(16), size = header.readUInt32LE(20);
      const commands = bytes(base + (magic === 0xfeedfacf ? 32 : 28), size);
      const name = (start: number, end: number): string => {
        const offset = commands.readUInt32LE(start + 8);
        if (offset < 12 || start + offset >= end) throw Error("a load command's name lies outside it");
        const nul = commands.indexOf(0, start + offset);
        return commands.toString("utf8", start + offset, nul < 0 || nul > end ? end : nul);
      };
      for (let i = 0, start = 0; i < count; i++) {
        if (start + 8 > size) throw Error("the load commands end early");
        const command = commands.readUInt32LE(start), length = commands.readUInt32LE(start + 4);
        if (length < 8 || start + length > size) throw Error("a load command's size is out of range");
        const unread = unreadCommands.get(command);
        if (unread !== undefined) throw Error(`it holds ${unread}`);
        if (dylibCommands.has(command)) libraries.push(name(start, start + length));
        if (command === runPathCommand) runPaths.push(name(start, start + length));
        start += length;
      }
      return { libraries, runPaths };
    };
    const magic = bytes(0, 4).readUInt32BE(0);
    if (magic === 0xcafebabe || magic === 0xcafebabf) {
      // A universal file: big-endian architecture entries, 32- or 64-bit offsets.
      const wide = magic === 0xcafebabf, width = wide ? 32 : 20;
      const count = bytes(4, 4).readUInt32BE(0);
      // dyld also loads an arm64 slice a 32-bit table describes right after
      // its last entry, outside its count.
      const entries = bytes(8, (count + (wide ? 0 : 1)) * width);
      const hidden = !wide && entries.readUInt32BE(count * width) === 0x0100000c ? 1 : 0;
      const slices = Array.from({ length: count + hidden }, (_, i) =>
        image(wide ? Number(entries.readBigUInt64BE(i * width + 8)) : entries.readUInt32BE(i * width + 8)));
      // dyld loads one architecture; the others must agree with it.
      const first = slices[0];
      if (first === undefined) throw Error("a universal file without architectures");
      const named = (c: LoadCommands): string => JSON.stringify([c.libraries, c.runPaths]);
      if (slices.some((c) => named(c) !== named(first))) throw Error("its architectures differ in their libraries or run paths");
      found = first;
    } else found = image(0);
  } catch (error) {
    found = `its load commands are not read: ${error instanceof Error ? error.message : String(error)}`;
  } finally {
    closeSync(descriptor);
  }
  if (fileDigest(file) === digest) loadCommandsOf.set(digest, found);
  return found;
}

/** A library name relative to its loader, resolved, or null. */
function resolveLoaderName(name: string, loader: string, executable: string, loaderRunPaths: readonly string[]):
    string | null {
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
  let executableRunPaths: readonly string[] = [];
  if (loader !== executable) {
    const commands = loadCommands(executable, fileDigest(executable));
    if (typeof commands === "string") return null;
    executableRunPaths = commands.runPaths;
  }
  for (const base of [...loaderRunPaths, ...executableRunPaths]) {
    const path = resolve(expand(base), rest);
    if (exists(path)) return path;
  }
  return null;
}

/** The mutation verifiers this process runs, by real path: builds of the
 * verifier with test-only mutations (`evidence-mutations.mts`), audited as
 * the verifier is. */
const mutationBuilds = new Set<string>();
/** Treat `executable`, a mutation verifier built from the repository's
 * verifier build, as an audited program: its I/O is the verifier's, and the
 * variable `TSCERT_TEST_MUTATIONS`, which its invocation's environment fixes. */
export function auditMutationVerifier(executable: string): void {
  mutationBuilds.add(realpathSync(executable));
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
 * a stand-in for an injected failure) has dependencies that are not
 * identified. A mutation verifier (`auditMutationVerifier`) is audited as
 * the verifier is, beside the one variable that selects its mutations. */
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
  const builds = mutationBuilds.has(real) || [verifierBuild, producerBuild].some((b) => {
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

/** The runner's identity: its executable and linked libraries by content,
 * and the platform; or why it has none. */
function runnerIdentity(): { identity: Canonical } | { unidentified: string } {
  let real: string;
  try {
    real = realpathSync(runnerBuild);
  } catch {
    return { unidentified: "the stage runner is not built (make build-runner)" };
  }
  const linked = linkedLibraries(real);
  if (typeof linked === "string") return { unidentified: `the stage runner: ${linked}` };
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
export function nodeIdentity(): { identity: Canonical } | { unidentified: string } {
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

/** The largest output a stage may print. */
const maxBuffer = 16 * 1024 * 1024;
/** What, beside the limit, decides whether a process stage times out. */
export const resourcePolicy: string = canonical({ maxBuffer, killSignal: "SIGTERM", spawn: "spawnSync" });
export const text = (bytes: Buffer): string => new TextDecoder("utf-8").decode(bytes);

/** Whether a stage's exit is a finished result under its protocol. */
export function finishedExit(protocol: Protocol, status: number | null, stdout: string, stderr: string): boolean {
  if (status === 0) return true;
  const detail = stderr.trim() || stdout.trim();
  const lines = detail.split("\n");
  return protocol.refusal !== null && status === protocol.refusal.status &&
    detail.startsWith(protocol.refusal.prefix) && lines.at(-1) === refusalEnd;
}

/** A file's bytes, or null where its path names nothing. */
export function readOrAbsent(path: string): Buffer | null {
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

/** A process invocation as bound: the program as the caller's working
 * directory names it, its argument vector, environment and exit protocol,
 * its input files by role, its outputs, its input description (whose
 * canonical text a key is the digest of), and why it is not
 * replay-eligible, or null. */
export type BoundProcess = {
  program: string;
  argv: readonly string[];
  environment: Readonly<Record<string, string>>;
  protocol: Protocol;
  inputFiles: readonly (readonly [string, Buffer])[];
  outputs: readonly { role: string; path: string }[];
  manifest: Canonical;
  input: string;
  ineligible: string | null;
};

/** Bind a process call: each input file read by content under its role's
 * name, each output at its role's name or, at an input's path, at that
 * input's; its description names the stage, this adapter's code, the
 * runtime, the executable, the runner, the argument vector, the environment, the exit
 * protocol, the input digests and the output roles. */
export function bindProcess(call: ProcessCall): BoundProcess {
  const program = resolve(call.program);
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
  const runner = runnerIdentity();
  const runtime = nodeIdentity();
  const manifest: Canonical = {
    stage: call.stage,
    code: "identity" in processCode ? processCode.identity : null,
    runtime: "identity" in runtime ? runtime.identity : null,
    implementation: "identity" in implementation ? implementation.identity : null,
    runner: "identity" in runner ? runner.identity : null,
    argv,
    environment: call.environment,
    protocol: call.protocol.refusal === null ? null
      : { status: call.protocol.refusal.status, prefix: call.protocol.refusal.prefix },
    inputs,
    outputs: outputs.map((o) => o.role),
  };
  const ineligible = codeFailure(processCode)
    ?? ("unidentified" in implementation ? implementation.unidentified
      : "unidentified" in runner ? runner.unidentified
      : "unidentified" in runtime ? runtime.unidentified : null);
  return { program, argv, environment: call.environment, protocol: call.protocol, inputFiles, outputs, manifest,
    input: canonical(manifest), ineligible };
}

/** A fresh directory for a process stage of `stage` to run in. */
export const executionDirectory = (stage: StageName): string => runDirectory(`stage-${stage}-`);

/** How a run ended: a finished result, the expiry of its own limit, or an
 * operational failure (a signal, an exit outside its protocol, a spawn
 * failure). */
export type Ran = "executed" | "timed-out" | "failed";

/** A process stage's run: how it ended, its exit, its output bytes and
 * text, and the output files it wrote, by role. */
export type ProcessRun = {
  ran: Ran;
  status: number | null;
  signal: NodeJS.Signals | null;
  error: Error | undefined;
  stdoutBytes: Buffer;
  stderrBytes: Buffer;
  stdout: string;
  stderr: string;
  produced: [string, Buffer][];
  /** The CPU time of the stage's processes, up to their end or their kill. */
  cpu: Cpu;
};

/** The runner's report (`runner/stage-runner.c`): the errno of a program
 * that did not execute, and the CPU time of the stage's processes. */
function readReport(report: string): { execErrno: number | null; cpu: Cpu } {
  const exec = /^exec (\d+)$/m.exec(report);
  const used = /^cpu (\d+) (\d+) (\d+)$/m.exec(report);
  return { execErrno: exec ? Number(exec[1]) : null,
    cpu: used ? { userMs: Number(used[1]) / 1000, systemMs: Number(used[2]) / 1000, peakBytes: Number(used[3]),
      covers: "the stage's program and the descendants it waited for" }
      : { unavailable: "the stage runner reported no CPU time" } };
}
const errnoNames = new Map(Object.entries(constants.errno).map(([name, n]) => [n, name]));

/** Run a bound process stage in `directory`, a fresh empty directory: its
 * inputs written there under their roles' names, the program run there with
 * the argument vector and the call's environment under the runner, killed at
 * `limitMs`, its exit classified by its protocol; its outputs delivered to
 * the caller's paths. The runner's report goes to a file unlinked before the
 * program starts, the runner's descriptor 3, which the program does not
 * inherit. */
export function executeProcess(bound: BoundProcess, directory: string, limitMs: number): ProcessRun {
  for (const [role, bytes] of bound.inputFiles) writeFileSync(join(directory, role), bytes);
  const reportPath = `${directory}.report`;
  const reportFile = openSync(reportPath, "w+");
  let p: ReturnType<typeof spawnSync>, report: string;
  try {
    unlinkSync(reportPath);
    p = spawnSync(runnerBuild, [bound.program, ...bound.argv], {
      cwd: directory,
      env: { ...bound.environment },
      timeout: limitMs,
      maxBuffer,
      stdio: ["pipe", "pipe", "pipe", reportFile],
    });
    const bytes = Buffer.alloc(fstatSync(reportFile).size);
    readSync(reportFile, bytes, 0, bytes.length, 0);
    report = bytes.toString("utf8");
  } finally {
    closeSync(reportFile);
  }
  if (p.error && "code" in p.error && p.error.code === "ENOENT" && p.error.message.includes(runnerBuild))
    throw Error("the stage runner is not built (make build-runner)");
  const { execErrno, cpu } = readReport(report);
  // A program that did not execute fails as a spawn failure does.
  const error = p.error ?? (execErrno === null ? undefined
    : Object.assign(Error(`spawnSync ${bound.program} ${errnoNames.get(execErrno) ?? execErrno}`),
      { code: errnoNames.get(execErrno) ?? String(execErrno), errno: -execErrno }));
  const status = execErrno === null ? p.status : null;
  const stdoutBytes = p.stdout ? Buffer.from(p.stdout) : Buffer.alloc(0);
  const stderrBytes = p.stderr ? Buffer.from(p.stderr) : Buffer.alloc(0);
  const stdout = text(stdoutBytes), stderr = text(stderrBytes);
  // A timeout is the expiry of this attempt's own enforced limit.
  const timedOut = (p.error && "code" in p.error && p.error.code === "ETIMEDOUT") ?? false;
  const finished = !error && !p.signal && status !== null && finishedExit(bound.protocol, status, stdout, stderr);
  const produced: [string, Buffer][] = [];
  for (const o of bound.outputs) {
    const bytes = readOrAbsent(join(directory, o.role));
    if (bytes !== null) produced.push([o.role, bytes]);
  }
  deliver(bound, produced);
  return { ran: timedOut ? "timed-out" : finished ? "executed" : "failed", status, signal: p.signal,
    error, stdoutBytes, stderrBytes, stdout, stderr, produced, cpu };
}

/** Write a stage's output files, by role, to the caller's paths. */
export function deliver(bound: BoundProcess, produced: readonly (readonly [string, Buffer])[]): void {
  const byRole = new Map(produced);
  for (const o of bound.outputs) {
    const bytes = byRole.get(o.role);
    if (bytes !== undefined) writeFileSync(o.path, bytes);
  }
}
