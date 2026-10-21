/* Part of the trusted front end: every file-system operation it makes, in one
 * place, and the record of what each one observed (DESIGN.md, "Observed
 * stages"). Whatever an operation throws is an `IoFailure` naming the
 * operation and the path, a tool failure by where it came from, whatever its
 * fields (Node's permission model throws ERR_ACCESS_DENIED with no
 * `syscall`). The one exception is `orAbsent`, where a path that names
 * nothing (ENOENT, or ENOTDIR for a path through a file) is an absence its
 * caller gives a meaning.
 *
 * Every read answers an observation: an operation, the absolute path it was
 * made at and its answer. The answers given while `observed` runs are its
 * observations; a read the record cannot account for (`unobservable`) makes
 * them incomplete. Node's resolver and loader cache what they read for the
 * process's lifetime: the process keeps the first answer of each of their
 * observations, and a later different answer means those caches may
 * disagree with the file system (`observed` reports it). */
import { createHash } from "node:crypto";
import { chmodSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, realpathSync, rmSync, statSync, writeFileSync,
  type Dirent } from "node:fs";
import { createRequire, isBuiltin, registerHooks } from "node:module";
import { tmpdir } from "node:os";
import { basename, dirname, join, relative, sep } from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { fieldOf, IoFailure } from "./thrown.mts";

/** `run`, its failure an `IoFailure` of `operation` at `path`. */
function io<T>(operation: string, path: string, run: () => T): T {
  try {
    return run();
  } catch (error) {
    throw error instanceof IoFailure ? error : new IoFailure(operation, path, error);
  }
}

const sha256 = (bytes: string | Uint8Array): string => createHash("sha256").update(bytes).digest("hex");
/** Whether `error` is the absence of what a path names. */
const absence = (error: unknown): boolean => {
  const code = fieldOf(error, "code");
  return code === "ENOENT" || code === "ENOTDIR";
};
/** An absence, thrown as the file system throws one. */
const absent = (what: string): Error => Object.assign(Error(`ENOENT: no such ${what}`), { code: "ENOENT" });
/** Names in the order the compiler's file system lists them: by their
 * UTF-8 bytes. */
const byBytes = (a: string, b: string): number => Buffer.compare(Buffer.from(a), Buffer.from(b));

// ---------------------------------------------------------------------------
// Observations

/** The operations an observation is made by: a file's bytes; what a path
 * names, links followed; its real path; a directory's entries with their own
 * kinds; a directory's files and directories as the compiler lists them,
 * links followed. */
export type Operation = "read" | "kind" | "real" | "dirents" | "entries";
const operations: readonly Operation[] = ["read", "kind", "real", "dirents", "entries"];
export const isOperation = (value: unknown): value is Operation => operations.some((o) => o === value);

/** An observation: its operation, the absolute path and the answer, null
 * where the path names nothing. */
export type Observation = readonly [Operation, string, string | null];

/** An answer as noted: its observation, and whether Node's resolver or
 * loader may hold it in a cache. */
type Noted = { observation: Observation; node: boolean };
/** A record being made: the answers by operation and path, the cached
 * values whose observations it holds, why it is incomplete, if it is, and
 * why Node's caches may disagree with the file system, if they may. */
type Recording = { answers: Map<string, Noted>; holding: Set<object>; incomplete: string | null;
  inconsistent: string | null };
const recordings: Recording[] = [];
/** The outermost records made in this process so far. */
let epoch: number = 0;
/** The first answer of each observation of Node's resolver and loader in
 * this process. */
const firstAnswers = new Map<string, string | null>();

/** Note an answer in each record being made, and, for Node's reads, in the
 * process's first answers: one of Node's differing from its first makes the
 * records inconsistent. */
function note(operation: Operation, path: string, answer: string | null, node: boolean): void {
  if (node) {
    const key = `${operation}\0${path}`;
    const first = firstAnswers.get(key);
    if (first === undefined) firstAnswers.set(key, answer);
    else if (first !== answer) inconsistent(`${operation} ${path} answers otherwise than when Node first read it`);
  }
  for (const recording of recordings) noteIn(recording, [operation, path, answer], node);
}
/** Note an answer in one record: one differing from an earlier answer of
 * the record makes it incomplete. */
function noteIn(recording: Recording, observation: Observation, node: boolean): void {
  const [operation, path, answer] = observation;
  const key = `${operation}\0${path}`;
  const known = recording.answers.get(key);
  if (known && known.observation[2] !== answer)
    recording.incomplete ??= `${operation} ${path} answered differently within the stage`;
  else recording.answers.set(key, { observation, node: node || (known?.node ?? false) });
}

/** Every record being made is incomplete, for `reason`: a read it cannot
 * account for. */
export function unobservable(reason: string): void {
  for (const recording of recordings) recording.incomplete ??= reason;
}
/** Why Node's caches in this process may disagree with the file system,
 * once they may: from then on every record is inconsistent. */
let staleProcess: string | null = null;
export const processInconsistency = (): string | null => staleProcess;
/** Why a Node read cannot be accounted for: the current stage may finish,
 * but further execution needs a fresh process. */
let retiringProcess: string | null = null;
export const processRetirement = (): string | null => retiringProcess;
function nodeUnobservable(reason: string): void {
  retiringProcess ??= reason;
  unobservable(reason);
}
/** The process, and every record being made, inconsistent, for `reason`. */
function inconsistent(reason: string): void {
  staleProcess ??= reason;
  for (const recording of recordings) recording.inconsistent ??= reason;
}

/** What `observed` gives: the value, the observations in a canonical order,
 * why they are incomplete, if they are, and why Node's caches may disagree
 * with the file system, if they may. */
export type Observed<T> = { value: T; observations: Observation[]; incomplete: string | null;
  inconsistent: string | null };
/** `run`, with the observations it made. */
export function observed<T>(run: () => T): Observed<T> {
  if (recordings.length === 0 && retiringProcess !== null)
    throw Error(`Node's reads are incomplete (${retiringProcess}); a fresh process is needed`);
  const made = observedNoting(run, true);
  return { value: made.value, observations: made.noted.map((n) => n.observation), incomplete: made.incomplete,
    inconsistent: made.inconsistent };
}
function observedNoting<T>(run: () => T, stage: boolean):
    { value: T; noted: Noted[]; incomplete: string | null; inconsistent: string | null } {
  if (stage && recordings.length === 0) epoch++;
  const recording: Recording = { answers: new Map(), holding: new Set(), incomplete: null, inconsistent: staleProcess };
  recordings.push(recording);
  let value: T;
  try {
    value = run();
  } finally {
    recordings.splice(recordings.indexOf(recording), 1);
  }
  const noted = [...recording.answers.values()].sort((a, b) => {
    const [x, y] = [a.observation, b.observation];
    return x[0] === y[0] ? byBytes(x[1], y[1]) : x[0] < y[0] ? -1 : 1;
  });
  return { value, noted, incomplete: recording.incomplete, inconsistent: recording.inconsistent };
}

/** The answer `operation` gives at `path` now, read afresh and noted. */
function answerOf(operation: Operation, path: string, node: boolean): string | null {
  switch (operation) {
    case "read": return readAnswer(path, node).answer;
    case "kind": return kindOf(path, node);
    case "real": return realOf(path, node);
    case "dirents": return direntsOf(path).answer;
    case "entries": return entriesOf(path).answer;
  }
}
const holds = (n: Noted): boolean => {
  try {
    return answerOf(n.observation[0], n.observation[1], n.node) === n.observation[2];
  } catch {
    return false;
  }
};

/** Whether every observation gives its answer when made again now. */
export function observationsHold(observations: readonly Observation[]): boolean {
  return observations.every((observation) => holds({ observation, node: false }));
}

/** A value of a process cache, with the observations it was computed from
 * and the outermost record during which they were last made. */
export type Remembered<V> = { value: V; noted: readonly Noted[]; incomplete: string | null; epoch: number };

/** The value `compute` gives for `key`, kept in `cache` with the
 * observations it was computed from: its first use during an outermost
 * record makes them again, computing the value again where one answers
 * otherwise, and every use notes them in the records being made, and
 * whether they are incomplete. */
export function remembered<K, V>(cache: Map<K, Remembered<V>>, key: K, compute: () => V): V {
  const known = cache.get(key);
  if (known && (known.epoch === epoch || known.noted.every(holds))) {
    known.epoch = epoch;
    if (known.incomplete !== null) unobservable(known.incomplete);
    for (const recording of recordings)
      if (!recording.holding.has(known)) {
        recording.holding.add(known);
        for (const n of known.noted) noteIn(recording, n.observation, n.node);
      }
    return known.value;
  }
  cache.delete(key);
  const made = observedNoting(compute, false);
  // What the computation noted is noted in the records around it already;
  // where it is incomplete or inconsistent, so are they.
  if (made.incomplete !== null) unobservable(made.incomplete);
  if (made.inconsistent !== null) inconsistent(made.inconsistent);
  const entry: Remembered<V> = { value: made.value, noted: made.noted, incomplete: made.incomplete, epoch };
  for (const recording of recordings) recording.holding.add(entry);
  cache.set(key, entry);
  return made.value;
}

// ---------------------------------------------------------------------------
// The operations

/** A file's bytes and its answer: its digest, `directory`, or null. */
function readAnswer(path: string, node: boolean): { bytes: Buffer | null; answer: string | null } {
  try {
    const bytes = readFileSync(path);
    const answer = sha256(bytes);
    note("read", path, answer, node);
    return { bytes, answer };
  } catch (error) {
    if (fieldOf(error, "code") === "EISDIR") {
      note("read", path, "directory", node);
      return { bytes: null, answer: "directory" };
    }
    if (!absence(error)) throw new IoFailure("read", path, error);
    note("read", path, null, node);
    return { bytes: null, answer: null };
  }
}
/** What a path names, links followed: a directory, any other file, or
 * nothing. */
function kindOf(path: string, node: boolean): "file" | "directory" | null {
  let answer: "file" | "directory" | null;
  try {
    answer = statSync(path).isDirectory() ? "directory" : "file";
  } catch (error) {
    if (!absence(error)) throw new IoFailure("stat", path, error);
    answer = null;
  }
  note("kind", path, answer, node);
  return answer;
}
/** A path's real path, every link resolved, or null. */
function realOf(path: string, node: boolean): string | null {
  let answer: string | null;
  try {
    answer = realpathSync(path);
  } catch (error) {
    if (!absence(error)) throw new IoFailure("resolve", path, error);
    answer = null;
  }
  note("real", path, answer, node);
  return answer;
}
/** A directory's entries, by name, each with its own kind. */
function direntsOf(path: string): { entries: Dirent[] | null; answer: string | null } {
  let entries: Dirent[] | null;
  try {
    entries = readdirSync(path, { withFileTypes: true }).sort((a, b) => byBytes(a.name, b.name));
  } catch (error) {
    if (!absence(error)) throw new IoFailure("list", path, error);
    entries = null;
  }
  const kind = (e: Dirent): string => e.isSymbolicLink() ? "l" : e.isDirectory() ? "d" : e.isFile() ? "f" : "o";
  const answer = entries === null ? null : sha256(JSON.stringify(entries.map((e) => [e.name, kind(e)])));
  note("dirents", path, answer, false);
  return { entries, answer };
}
/** A directory's files and directories as the compiler's own file system
 * lists them: by name, a link by what it names, a link naming nothing and
 * any other entry left out; nothing where the directory is absent. */
type Entries = { files: string[]; directories: string[] };
function entriesOf(path: string): { entries: Entries; answer: string | null } {
  let listed: Dirent[];
  try {
    listed = readdirSync(path, { withFileTypes: true }).sort((a, b) => byBytes(a.name, b.name));
  } catch (error) {
    if (!absence(error)) throw new IoFailure("list", path, error);
    note("entries", path, null, false);
    return { entries: { files: [], directories: [] }, answer: null };
  }
  const files: string[] = [], directories: string[] = [];
  for (const e of listed) {
    let directory = e.isDirectory(), file = e.isFile();
    if (e.isSymbolicLink()) {
      try {
        const target = statSync(join(path, e.name));
        directory = target.isDirectory();
        file = target.isFile();
      } catch {
        directory = file = false;
      }
    }
    if (directory) directories.push(e.name);
    else if (file) files.push(e.name);
  }
  const entries = { files, directories };
  const answer = sha256(JSON.stringify(entries));
  note("entries", path, answer, false);
  return { entries, answer };
}

/** A file's text, as UTF-8. */
export const readText = (path: string): string => readBytes(path).toString("utf8");
/** A file's bytes. */
export function readBytes(path: string): Buffer {
  return io("read", path, () => {
    const { bytes, answer } = readAnswer(path, false);
    if (bytes) return bytes;
    throw answer === "directory" ? Object.assign(Error("EISDIR: a directory"), { code: "EISDIR" }) : absent("file");
  });
}
/** A path's real path, every link resolved. */
export function realPath(path: string): string {
  return io("resolve", path, () => {
    const real = realOf(path, false);
    if (real !== null) return real;
    throw absent("file or directory");
  });
}
/** A directory's entries. */
export function listDirectory(path: string): Dirent[] {
  return io("list", path, () => {
    const { entries } = direntsOf(path);
    if (entries) return entries;
    throw absent("directory");
  });
}

/** Write `text` to the file at `path`: for a command's output, never read
 * back by a stage. */
export const writeText = (path: string, text: string): void => io("write", path, () => writeFileSync(path, text));

/** The value of one of the operations above, run as `operation`, or null
 * where its path names nothing. */
export function orAbsent<T>(operation: (path: string) => T, path: string): T | null {
  try {
    return operation(path);
  } catch (error) {
    const cause = error instanceof IoFailure ? error.cause : error;
    if (absence(cause)) return null;
    throw error;
  }
}
/** Whether a path names a file or directory: false only where it names
 * nothing, any other failure of the file system thrown on. */
export const present = (path: string): boolean => io("stat", path, () => kindOf(path, false)) !== null;

// ---------------------------------------------------------------------------
// The implementation's identity

/** A file's digest, kept within the process while its device, inode, size,
 * modification and change times are unchanged: the kernel sets the change
 * time on every write. The rule of the stage store's executable digests,
 * used for the implementation's identity, never for an observation. */
const fileDigests = new Map<string, { signature: string; digest: string }>();
function fileDigest(path: string): string {
  const s = statSync(path, { bigint: true });
  const signature = `${s.dev}:${s.ino}:${s.size}:${s.mtimeNs}:${s.ctimeNs}`;
  const known = fileDigests.get(path);
  if (known?.signature === signature) return known.digest;
  const digest = sha256(readFileSync(path));
  fileDigests.set(path, { signature, digest });
  return digest;
}
/** The digest of the tree at `path`, links followed: a file by its content,
 * a directory by its entries' names and digests in name order, anything
 * else by its kind; null where the path names nothing. A link cycle is a
 * failure. Unobserved: the implementation's identity. */
export function treeDigest(path: string): string | null {
  const walk = (at: string, above: readonly string[]): string | null => {
    try {
      const s = statSync(at);
      if (!s.isDirectory()) return s.isFile() ? `f${fileDigest(at)}` : "o";
    } catch (error) {
      if (absence(error)) return null;
      throw error;
    }
    const real = realpathSync(at);
    if (above.includes(real)) throw Error(`a link cycle at ${at}`);
    const names = readdirSync(at).sort(byBytes);
    return `d${sha256(names.map((n) => `${n}\0${walk(join(at, n), [...above, real]) ?? "-"}`).join("\0"))}`;
  };
  return io("digest", path, () => walk(path, []));
}
/** Whether a file exists, unobserved: for the compiler's installation, which
 * the implementation's identity covers. */
export function installed(path: string): boolean {
  try {
    return statSync(path).isFile();
  } catch {
    return false;
  }
}

// ---------------------------------------------------------------------------
// The compiler's file system

/** The compiler API's file-system queries (`typescript/unstable/fs`), each
 * answered here and never declined, so the compiler falls back to its own
 * file system for none of them. */
export type CompilerFileSystem = {
  readFile: (path: string) => string | null | undefined;
  fileExists: (path: string) => boolean | undefined;
  directoryExists: (path: string) => boolean | undefined;
  getAccessibleEntries: (path: string) => Entries | undefined;
  realpath: (path: string) => string | undefined;
};

/** A file's text as the compiler's own file system decodes its bytes: a
 * UTF-16 byte order mark decodes the rest as UTF-16, a UTF-8 one is
 * dropped, and other bytes are UTF-8, which they must be. */
function compilerText(path: string, bytes: Buffer): string {
  const utf16 = (encoding: string): string =>
    new TextDecoder(encoding).decode(bytes.subarray(2, 2 + ((bytes.length - 2) & ~1)));
  if (bytes[0] === 0xff && bytes[1] === 0xfe) return utf16("utf-16le");
  if (bytes[0] === 0xfe && bytes[1] === 0xff) return utf16("utf-16be");
  const utf8 = bytes[0] === 0xef && bytes[1] === 0xbb && bytes[2] === 0xbf ? bytes.subarray(3) : bytes;
  return io("decode", path, () => new TextDecoder("utf-8", { fatal: true }).decode(utf8));
}

/** The compiler's file system: the texts of `overlay` at their paths; a path
 * inside `installation`, the compiler's own installation, which the
 * implementation's identity covers, declined, for the compiler to read
 * itself; every other answer an observation of exactly that answer. */
export function compilerFileSystem(overlay: ReadonlyMap<string, string>, installation: string | null):
    CompilerFileSystem {
  const own = (path: string): boolean => installation !== null && path.startsWith(installation + sep);
  return {
    readFile: (path: string): string | null | undefined => kept(() => {
      const held = overlay.get(path);
      if (held !== undefined) return held;
      if (own(path)) return undefined;
      const { bytes } = io("read", path, () => readAnswer(path, false));
      return bytes ? compilerText(path, bytes) : null;
    }),
    fileExists: (path: string): boolean | undefined => kept(() =>
      overlay.has(path) || (own(path) ? undefined : io("stat", path, () => kindOf(path, false)) === "file")),
    directoryExists: (path: string): boolean | undefined => kept(() =>
      own(path) ? undefined : io("stat", path, () => kindOf(path, false)) === "directory"),
    getAccessibleEntries: (path: string): Entries | undefined => kept(() =>
      own(path) ? undefined : io("list", path, () => entriesOf(path)).entries),
    realpath: (path: string): string | undefined => kept(() =>
      own(path) ? undefined : io("resolve", path, () => realOf(path, false)) ?? path),
  };
}
/** A query's failure, kept for the request it fails (`takeQueryFailure`):
 * the compiler sees only its message. */
function kept<T>(query: () => T): T {
  try {
    return query();
  } catch (error) {
    queryFailure ??= error;
    throw error;
  }
}
/** The first failure of a compiler's file-system query since the last call. */
let queryFailure: unknown = null;
export function takeQueryFailure(): unknown {
  const failure = queryFailure;
  queryFailure = null;
  return failure;
}

/** A directory of this process's own, removed when it exits. */
let ownDirectory: string | null = null;
function privateDirectory(): string {
  if (ownDirectory) return ownDirectory;
  const made = realpathSync(mkdtempSync(join(tmpdir(), "tscert-compiler-")));
  process.on("exit", () => rmSync(made, { recursive: true, force: true }));
  ownDirectory = made;
  return made;
}
/** An executable script whose text `text` gives from the paths of an empty
 * directory beside it and of the script itself, both this process's own and
 * real paths. */
export function privateLauncher(text: (directory: string, launcher: string) => string):
    { launcher: string; directory: string } {
  const root = privateDirectory();
  const directory = join(root, "cwd");
  const launcher = join(root, "compiler.sh");
  mkdirSync(directory, { recursive: true });
  writeFileSync(launcher, text(directory, launcher), { mode: 0o500 });
  chmodSync(launcher, 0o500);
  return { launcher, directory };
}

// ---------------------------------------------------------------------------
// Packages, Node's resolver and its loader

/** The package a bare specifier names: its scope and name. */
const packageOf = (specifier: string): string =>
  specifier.split("/").slice(0, specifier.startsWith("@") ? 2 : 1).join("/");
/** `directory` and each directory above it, nearest first. */
function ancestors(directory: string): string[] {
  const found = [directory];
  for (let at = directory; dirname(at) !== at; at = dirname(at)) found.push(dirname(at));
  return found;
}

/** The directory of the package `name` that Node's `node_modules` lookup
 * finds from `directory` (REFERENCES.md, "Node.js modules"): the nearest
 * `node_modules/<name>` directory of `directory` or a directory above it,
 * by its real path, where it holds a manifest; else null. */
export function findPackage(name: string, directory: string): string | null {
  for (const at of ancestors(directory)) {
    const candidate = join(at, "node_modules", ...name.split("/"));
    if (kindOf(candidate, false) !== "directory") continue;
    return kindOf(join(candidate, "package.json"), false) === "file" ? realOf(candidate, false) : null;
  }
  return null;
}

/** A manifest's field, or undefined where it has none or is no JSON. */
function manifestField(bytes: Buffer | null, field: string): unknown {
  if (bytes === null) return undefined;
  try {
    const parsed: unknown = JSON.parse(bytes.toString("utf8"));
    return fieldOf(parsed, field);
  } catch {
    return undefined;
  }
}
/** The package scope of a module: the nearest `package.json` of its
 * directory or a directory above, read, as Node's loader finds it. */
function observeScope(module: string, checkLinks: boolean = false): { directory: string; bytes: Buffer | null } | null {
  for (const at of ancestors(dirname(module))) {
    if (basename(at) === "node_modules") break;
    const manifest = join(at, "package.json");
    if (kindOf(manifest, true) === "file") {
      if (checkLinks) observePackageLinks(at);
      return { directory: at, bytes: readAnswer(manifest, true).bytes };
    }
  }
  return null;
}
/** The entries of every directory of a package's own tree, links not
 * followed and nested `node_modules` left out, where Node's `exports` and
 * `imports` targets lie (a target naming `node_modules` is invalid): a
 * package holding a link there is not accounted for, since the path a target
 * names before Node resolves its links is not observed. */
function observePackageLinks(directory: string): void {
  const { entries } = direntsOf(directory);
  if (entries === null) {
    nodeUnobservable(`the package directory ${directory} is absent`);
    return;
  }
  for (const entry of entries) {
    if (entry.isSymbolicLink()) nodeUnobservable(`the package tree ${directory} contains a symbolic link`);
    else if (entry.isDirectory() && entry.name !== "node_modules") observePackageLinks(join(directory, entry.name));
  }
}
/** The reads of Node's resolution of `specifier` from the module at
 * `parent` (REFERENCES.md, "Node.js modules") before its target: for a bare
 * specifier, its package scope, which resolves a self-reference through its
 * `exports`, else its `node_modules` lookup, nearest first, up to the first
 * directory holding the package, and that package's manifest; for a package
 * import, its package scope; for a relative, absolute or `file:` specifier,
 * its target; for a built-in, nothing. A package without `exports` is not
 * accounted for. Whether a package or a scope resolves the specifier, so
 * that its target is to be found. */
function observeResolution(specifier: string, parent: string): { found: boolean; scope: string | null } {
  if (isBuiltin(specifier) || /^(node|data):/.test(specifier)) return { found: false, scope: null };
  // A package import resolves through its package scope's `imports`: to a
  // file of the scope's own tree, or through another package lookup, which
  // its target shows (`nodeResolve`).
  if (specifier.startsWith("#")) return { found: true, scope: observeScope(parent, true)?.directory ?? null };
  if (/^(\.{0,2}\/|file:)/.test(specifier)) {
    let target: string;
    try {
      target = fileURLToPath(new URL(specifier, pathToFileURL(parent)));
    } catch {
      return { found: false, scope: null };
    }
    kindOf(target, true);
    realOf(target, true);
    return { found: true, scope: null };
  }
  const name = packageOf(specifier);
  // A self-reference resolves through its package scope's `exports`.
  const scope = observeScope(parent);
  if (scope && manifestField(scope.bytes, "name") === name && manifestField(scope.bytes, "exports") != null) {
    observeScope(parent, true);
    return { found: true, scope: null };
  }
  for (const at of ancestors(dirname(parent))) {
    const candidate = join(at, "node_modules", ...name.split("/"));
    if (kindOf(candidate, true) !== "directory") continue;
    realOf(candidate, true);
    observePackageLinks(candidate);
    if (manifestField(readAnswer(join(candidate, "package.json"), true).bytes, "exports") == null)
      nodeUnobservable(`the package ${name} of ${specifier} states no exports`);
    return { found: true, scope: null };
  }
  return { found: false, scope: null };
}

/** The URL Node's own ES module resolver resolves `specifier` to from the
 * module at `parent`, under the conditions it enables in this process: a
 * file URL with no query or fragment, else `null`, as where Node throws.
 * Run through a resolve hook, which calls Node's resolution with that parent
 * and resolves nothing else; it loads nothing. Its reads are observed before
 * and after it, and must agree; its target after it. */
export function nodeResolve(specifier: string, parent: string): string | null {
  const before = observedNoting(() => observeResolution(specifier, parent), false);
  const probe = "tscert:resolve";
  const found: { url: string | null } = { url: null };
  const hooks = registerHooks({
    resolve: (requested, context, next) => {
      if (requested !== probe) return next(requested, context);
      try {
        found.url = next(specifier, { ...context, parentURL: pathToFileURL(parent).href }).url;
      } catch {
        found.url = null;
      }
      return { url: "data:text/javascript,", shortCircuit: true };
    },
  });
  try {
    import.meta.resolve(probe);
  } finally {
    hooks.deregister();
  }
  const after = observedNoting(() => observeResolution(specifier, parent), false);
  if (JSON.stringify(before.noted) !== JSON.stringify(after.noted))
    inconsistent(`the files Node read resolving ${specifier} from ${parent} changed meanwhile`);
  const url = found.url;
  const parsed = url === null ? null : new URL(url);
  if (parsed?.protocol === "file:") {
    const target = fileURLToPath(parsed);
    kindOf(target, true);
    realOf(target, true);
    // A package import's target is the scope's own file, outside any
    // `node_modules`; one reached through another package lookup is not
    // accounted for.
    const scope = after.value.scope === null ? null : realOf(after.value.scope, true);
    const real = realOf(target, true);
    const within = scope === null || real === null ? null : relative(scope, real).split(sep);
    if (specifier.startsWith("#") && (within === null || within[0] === ".." || within.includes("node_modules")))
      nodeUnobservable(`the package import ${specifier} resolves outside its package scope's own files`);
  } else if (after.value.found && !/^(\.{0,2}\/|file:)/.test(specifier))
    nodeUnobservable(`${specifier} is unresolved in the package found for it`);
  // A query or a fragment names another instance of the same file: refused.
  return parsed && parsed.protocol === "file:" && parsed.search === "" && parsed.hash === "" ? url : null;
}

/** The conditions Node's ES module resolution enables in this process
 * (`node`, `import`, `module-sync` and `node-addons` by default, and any
 * `--conditions`), read from the resolution itself through a resolve hook,
 * with `default`, which every resolution admits. */
let runtimeConditionsRead: readonly string[] | null = null;
export function runtimeConditions(): readonly string[] {
  if (runtimeConditionsRead) return runtimeConditionsRead;
  const probe = "tscert:conditions";
  const seen: { conditions: readonly string[] | null } = { conditions: null };
  const hooks = registerHooks({
    resolve: (specifier, context, next) => {
      if (specifier !== probe) return next(specifier, context);
      seen.conditions = context.conditions;
      return { url: "data:text/javascript,", shortCircuit: true };
    },
  });
  try {
    import.meta.resolve(probe);
  } finally {
    hooks.deregister();
  }
  const read = seen.conditions;
  if (read === null) throw Error("the resolve hook saw no resolution of the conditions probe");
  runtimeConditionsRead = [...read, "default"];
  return runtimeConditionsRead;
}

/** Node's loader for a module by its path: `require` of an ES module, which
 * shares the instance an `import` of the same file loads. */
const requireModule: (path: string) => unknown = createRequire(import.meta.url);

/** The module at `path` of the installation at `root` (a real path), as
 * Node loads it: the bytes of each module the load reads, as a load hook
 * sees them, and its package scope are observed; a module read outside the
 * installation is not accounted for. */
export function loadModule(root: string, path: string): unknown {
  const loaded: { url: string; source: unknown }[] = [];
  const hooks = registerHooks({
    load: (url, context, next) => {
      const result = next(url, context);
      loaded.push({ url, source: result.source });
      return result;
    },
  });
  try {
    return requireModule(path);
  } finally {
    hooks.deregister();
    for (const { url, source } of loaded) {
      if (url.startsWith("node:")) continue;
      const file = url.startsWith("file:") ? fileURLToPath(url) : null;
      const real = file === null ? null : realOf(file, true);
      if (file === null || real === null || relative(root, real).split(sep)[0] === "..") {
        nodeUnobservable(`loading ${path} read ${url}, outside its installation`);
        continue;
      }
      observeScope(file);
      if (source instanceof Uint8Array || typeof source === "string") note("read", file, sha256(source), true);
      else readAnswer(file, true);
    }
  }
}
