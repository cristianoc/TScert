/* Part of the trusted front end: every file-system operation it makes, in one
 * place, and the record of what each one observed (STAGE-STORE.md, "Observed
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
  type BigIntStats, type Dirent } from "node:fs";
import { isBuiltin } from "node:module";
import { tmpdir } from "node:os";
import { basename, dirname, join, relative, sep } from "node:path";
import { fileURLToPath } from "node:url";
import type { Json } from "./calculus.mts";
import { fieldOf, ioFailure, ioFailureOf } from "./thrown.mts";
import { loadObserved, resolutionConditions, resolveWithNode } from "./module-hooks.mts";
import { pathToFileHref, resolveHref } from "./url-strings.mts";

/** `run`, its failure an `IoFailure` of `operation` at `path`. */
function io<T>(operation: string, path: string, run: () => T): T {
  try {
    return run();
  } catch (error) {
    throw ioFailureOf(error) ? error : ioFailure(operation, path, error);
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
const byBytes = (a: string, b: string): number =>
  // Below U+D800 the order of UTF-16 code units is that of UTF-8 bytes.
  !/[\ud800-￿]/.test(a) && !/[\ud800-￿]/.test(b) ? (a < b ? -1 : a > b ? 1 : 0)
    : Buffer.compare(Buffer.from(a), Buffer.from(b));

// ---------------------------------------------------------------------------
// Observations

/** The operations an observation is made by: a file's bytes; what a path
 * names, links followed; its real path; a directory's entries with their own
 * kinds; a directory's files and directories as the compiler lists them,
 * links followed. */
export type Operation = "read" | "kind" | "real" | "dirents" | "entries" | "input";
const operations: readonly Operation[] = ["read", "kind", "real", "dirents", "entries", "input"];
export const isOperation = (value: unknown): value is Operation => operations.some((o) => o === value);

/** An observation: its operation, the absolute path and the answer, null
 * where the path names nothing. */
export type Observation = readonly [Operation, string, string | null];

/** An answer as noted: its observation, and whether Node's resolver or
 * loader may hold it in a cache. */
export type Noted = { observation: Observation; node: boolean };
/** A record being made: the answers by operation and path, the cached
 * values whose observations it holds, why it is incomplete, if it is, and
 * why Node's caches may disagree with the file system, if they may. */
export type Recording = { answers: Map<string, Noted>; holding: Set<object>; incomplete: string | null; ledger: boolean;
  inconsistent: string | null; stage?: true; readsInput?: true };
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

/** A read of the innermost stage's named input `name` (STAGE-STORE.md,
 * "Shared work"), an observation `["input", name, answer]` of that stage's
 * record alone: the stage's invocation evaluates it again before a replay,
 * and before it publishes. An enclosing stage's record computed the input
 * from reads of its own, and holds none. Every record of a process cache's
 * computation being made, within the stage or around it, is incomplete and
 * computed from a named input: its value is kept for none. */
export function noteInput(name: string, answer: string): void {
  let at = recordings.length - 1;
  while (at >= 0 && recordings[at]?.stage !== true) at--;
  const owner = recordings[at];
  if (owner) noteIn(owner, ["input", name, answer], false);
  inputRead(name);
}
/** A named input `name` read, by a stage executed or replayed: every process
 * cache's computation being made is incomplete and kept for none. */
export function inputRead(name: string): void {
  for (const r of recordings)
    if (r.stage !== true && !r.ledger) {
      r.incomplete ??= `a named input (${name}) read by a record no invocation evaluates`;
      r.readsInput = true;
    }
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
  const made = observedNoting(run, true, true);
  return { value: made.value, observations: made.noted.map((n) => n.observation), incomplete: made.incomplete,
    inconsistent: made.inconsistent };
}
function observedNoting<T>(run: () => T, stage: boolean, inherit: boolean):
    { value: T; noted: Noted[]; incomplete: string | null; inconsistent: string | null; readsInput: boolean } {
  if (stage && recordings.length === 0) epoch++;
  const recording: Recording = { answers: new Map(), holding: new Set(), incomplete: null, inconsistent: staleProcess,
    ledger: false, ...(stage ? { stage: true } : {}) };
  // The outermost stage's record bounds the attempt's answers.
  const begins = stage && attempt === null;
  if (begins) attempt = attemptOf(recording);
  // A record begun while a compiler session's ledger is being kept holds the
  // ledger: what it computes may read the session's compiler, whose state
  // the ledger's answers determine.
  if (inherit) for (const kept of recordings) if (kept.ledger) inheritLedger(recording, kept);
  recordings.push(recording);
  const value = (() => {
    try {
      return run();
    } finally {
      recordings.splice(recordings.indexOf(recording), 1);
      if (begins) attempt = null;
    }
  })();
  const noted = [...recording.answers.values()].sort((a, b) => {
    const [x, y] = [a.observation, b.observation];
    return x[0] === y[0] ? byBytes(x[1], y[1]) : x[0] < y[0] ? -1 : 1;
  });
  return { value, noted, incomplete: recording.incomplete, inconsistent: recording.inconsistent,
    readsInput: recording.readsInput === true };
}

/** The answers of the attempt running (STAGE-STORE.md, "Shared work"), by
 * operation and path: the outermost stage's record being made, and each
 * answer the front end's own `kind`, `real`, `dirents` and `entries` gave
 * during it. The store assumes the file system stable while a stage reads
 * it; within the attempt such an operation at a path answers what it
 * answered first, noted again in every record being made, so the attempt's
 * computation is a function of the answers its observations record. Outside
 * every record, as while a ledger is validated, and for a read standing for
 * Node's, each operation reads afresh. */
let sharingOn: boolean = true;
/** How many probes around Node's own reads are running (`fresh`): their
 * reads are made afresh, so the probes before and after a Node operation
 * compare what the file system answers. */
let probing: number = 0;
function fresh<T>(run: () => T): T {
  probing++;
  try {
    return run();
  } finally {
    probing--;
  }
}
/** Whether work is shared (STAGE-STORE.md, "Shared work"): the attempt's
 * answers here and the compiler's query answers (`compiler-channel.mts`). */
export const sharing = (): boolean => sharingOn;
/** Tests only: `run` with work shared or not, for comparing the two. */
export function sharingForTests<T>(on: boolean, run: () => T): T {
  const was = sharingOn;
  sharingOn = on;
  try {
    return run();
  } finally {
    sharingOn = was;
  }
}
type Kind = "file" | "directory" | null;
type AttemptAnswers = { owner: Recording; kind: Map<string, { answer: Kind }>;
  real: Map<string, { answer: string | null }>; dirents: Map<string, Listed<Dirent[] | null>>;
  entries: Map<string, Listed<Entries>> };
type Listed<E> = { entries: E; answer: string | null };
let attempt: AttemptAnswers | null = null;
const attemptOf = (owner: Recording): AttemptAnswers =>
  ({ owner, kind: new Map(), real: new Map(), dirents: new Map(), entries: new Map() });
function attemptAnswer<R extends { readonly answer: string | null }>(answers: (a: AttemptAnswers) => Map<string, R>,
    operation: Operation, path: string, node: boolean, read: () => R): R {
  // A read standing for Node's is made afresh and not kept: Node's agreement
  // and the process's first answers compare what the file system answers.
  const live = !node && probing === 0 && sharingOn && attempt !== null && recordings.includes(attempt.owner)
    ? answers(attempt) : null;
  const known = live?.get(path);
  const result = known ?? read();
  if (live && !known) live.set(path, result);
  note(operation, path, result.answer, node);
  return result;
}

/** The answer `operation` gives at `path` now, read afresh and noted. */
function answerOf(operation: Operation, path: string, node: boolean): string | null {
  switch (operation) {
    // A named input's read is the invocation's to evaluate (`noteInput`).
    case "input": throw Error(`the named input ${path} is no file-system answer`);
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

/** A record kept over a compiler session's lifetime (STAGE-STORE.md,
 * "Retained declaration sessions"): every answer its compiler was given, each
 * with its Node-origin bit, why it is incomplete and why Node's caches may
 * disagree with the file system, if they may. */
export type Ledger = { readonly recording: Recording };
export const newLedger = (): Ledger =>
  ({ recording: { answers: new Map(), holding: new Set(), incomplete: null, inconsistent: staleProcess, ledger: true } });
/** The number of answers a ledger holds, and its state. */
export const ledgerState = (ledger: Ledger): { answers: number; incomplete: string | null; inconsistent: string | null } =>
  ({ answers: ledger.recording.answers.size, incomplete: ledger.recording.incomplete,
    inconsistent: ledger.recording.inconsistent });
/** A ledger's answers, each with its Node-origin bit, for the controls. */
export const ledgerAnswers = (ledger: Ledger): Noted[] => [...ledger.recording.answers.values()];
/** `run`, every answer it is given also noted in `ledger`. */
export function withLedger<T>(ledger: Ledger, run: () => T): T {
  if (recordings.includes(ledger.recording)) return run();
  recordings.push(ledger.recording);
  try {
    return run();
  } finally {
    recordings.splice(recordings.indexOf(ledger.recording), 1);
  }
}
/** Why `ledger` does not hold now, or null: its answers made again, each with
 * its Node-origin bit, outside every record being made, so that only the
 * process's first answers of Node's reads see them. A Node answer that
 * differs makes the process inconsistent, and so every record being made. */
export function validateLedger(ledger: Ledger): string | null {
  const { recording } = ledger;
  if (recording.incomplete !== null) return `the ledger is incomplete: ${recording.incomplete}`;
  if (recording.inconsistent !== null) return `the ledger is inconsistent: ${recording.inconsistent}`;
  const suspended = recordings.splice(0);
  let failed: string | null = null;
  try {
    // Every Node answer is made again, for the process's first answers to
    // see it, after the first answer that differs as well.
    for (const n of recording.answers.values())
      if ((failed === null || n.node) && !holds(n))
        failed ??= `${n.observation[0]} ${n.observation[1]} answers otherwise now`;
  } finally {
    recordings.push(...suspended);
  }
  if (staleProcess !== null) inconsistent(staleProcess);
  if (failed === null && staleProcess !== null) failed = `the process is inconsistent: ${staleProcess}`;
  if (failed === null && retiringProcess !== null) failed = `the process is retiring: ${retiringProcess}`;
  return failed;
}
/** Note every answer of `ledger`, with its Node-origin bit, its incompleteness
 * and its inconsistency in each record being made but the ledger's own that
 * does not hold it yet; a record begun while the ledger is kept
 * (`withLedger`) holds them from its start. Once per record: records are
 * made in a stack, and a ledger grows only while it is kept, so every later
 * answer, incompleteness or inconsistency of the ledger reaches every record
 * holding it that is still being made. */
export function importLedger(ledger: Ledger): void {
  for (const r of recordings) if (r !== ledger.recording) inheritLedger(r, ledger.recording);
}
function inheritLedger(into: Recording, kept: Recording): void {
  if (into.holding.has(kept)) return;
  into.holding.add(kept);
  for (const n of kept.answers.values()) noteIn(into, n.observation, n.node);
  if (kept.incomplete !== null) into.incomplete ??= kept.incomplete;
  if (kept.inconsistent !== null) into.inconsistent ??= kept.inconsistent;
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
  const made = observedNoting(compute, false, true);
  // What the computation noted is noted in the records around it already;
  // where it is incomplete or inconsistent, so are they.
  if (made.incomplete !== null) unobservable(made.incomplete);
  if (made.inconsistent !== null) inconsistent(made.inconsistent);
  // A value computed from a stage's named input is the stage's alone: kept
  // for none.
  if (made.readsInput) return made.value;
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
    if (!absence(error)) throw ioFailure("read", path, error);
    note("read", path, null, node);
    return { bytes: null, answer: null };
  }
}
/** What a path names, links followed: a directory, any other file, or
 * nothing. */
function kindOf(path: string, node: boolean): Kind {
  return attemptAnswer((a) => a.kind, "kind", path, node, (): { answer: Kind } => {
    try {
      return { answer: statSync(path).isDirectory() ? "directory" : "file" };
    } catch (error) {
      if (!absence(error)) throw ioFailure("stat", path, error);
      return { answer: null };
    }
  }).answer;
}
/** A path's real path, every link resolved, or null. */
function realOf(path: string, node: boolean): string | null {
  return attemptAnswer((a) => a.real, "real", path, node, (): { answer: string | null } => {
    try {
      return { answer: realpathSync(path) };
    } catch (error) {
      if (!absence(error)) throw ioFailure("resolve", path, error);
      return { answer: null };
    }
  }).answer;
}
/** A directory's entries, by name, each with its own kind. */
function direntsOf(path: string): Listed<Dirent[] | null> {
  return attemptAnswer((a) => a.dirents, "dirents", path, false, () => direntsRead(path));
}
function direntsRead(path: string): Listed<Dirent[] | null> {
  let entries: Dirent[] | null;
  try {
    entries = readdirSync(path, { withFileTypes: true }).sort((a, b) => byBytes(a.name, b.name));
  } catch (error) {
    if (!absence(error)) throw ioFailure("list", path, error);
    entries = null;
  }
  const kind = (e: Dirent): string => e.isSymbolicLink() ? "l" : e.isDirectory() ? "d" : e.isFile() ? "f" : "o";
  const answer = entries === null ? null : sha256(JSON.stringify(entries.map((e) => [e.name, kind(e)])));
  return { entries, answer };
}
/** A directory's files and directories as the compiler's own file system
 * lists them: by name, a link by what it names, a link naming nothing and
 * any other entry left out; nothing where the directory is absent. */
type Entries = { files: string[]; directories: string[] };
function entriesOf(path: string): Listed<Entries> {
  return attemptAnswer((a) => a.entries, "entries", path, false, () => entriesRead(path));
}
function entriesRead(path: string): Listed<Entries> {
  let listed: Dirent[];
  try {
    listed = readdirSync(path, { withFileTypes: true }).sort((a, b) => byBytes(a.name, b.name));
  } catch (error) {
    if (!absence(error)) throw ioFailure("list", path, error);
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
  const entries: Entries & { readonly [key: string]: readonly string[] } = { files, directories };
  const answer = sha256(JSON.stringify(entries));
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
    const failed = ioFailureOf(error);
    if (!absence(failed ? failed.cause : error)) throw error;
    return null;
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
function fileDigest(path: string, s: BigIntStats = statSync(path, { bigint: true })): string {
  const signature = `${s.dev}:${s.ino}:${s.size}:${s.mtimeNs}:${s.ctimeNs}`;
  const known = fileDigests.get(path);
  if (known?.signature === signature) return known.digest;
  const digest = sha256(readFileSync(path));
  fileDigests.set(path, { signature, digest });
  return digest;
}
/** The digest of the tree at `path`, links followed: a file by its content,
 * a directory by its entries' names and digests in name order, anything
 * else by its kind; null where the path names nothing. A link cycle (a
 * directory inside itself, by device and inode) is a failure. Unobserved:
 * the implementation's identity. */
export function treeDigest(path: string): string | null {
  const walk = (at: string, above: readonly string[]): string | null => {
    let s: BigIntStats;
    try {
      s = statSync(at, { bigint: true });
      if (!s.isDirectory()) return s.isFile() ? `f${fileDigest(at, s)}` : "o";
    } catch (error) {
      if (absence(error)) return null;
      throw error;
    }
    const self = `${s.dev}:${s.ino}`;
    if (above.includes(self)) throw Error(`a link cycle at ${at}`);
    const names = readdirSync(at).sort(byBytes);
    return `d${sha256(names.map((n) => `${n}\0${walk(join(at, n), [...above, self]) ?? "-"}`).join("\0"))}`;
  };
  return io("digest", path, () => walk(path, []));
}
/** Whether a file exists, unobserved: for the compiler's installation, which
 * the implementation's identity covers. A test's result is compared with
 * `true`: `isFile` dispatches through a prototype other code may change. */
export function installed(path: string): boolean {
  try {
    return statSync(path).isFile() === true;
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

/** A key of a package manifest the front end reads; `Object.prototype` and
 * `Array.prototype` hold none of them. */
export type ManifestKey = "name" | "version" | "exports" | "imports";
/** A package manifest's member at `key`, where the manifest, `JSON.parse`'s
 * result, is an object owning one; else undefined. A JSON array owns only
 * its indices and its length, so an array has no member. */
export function manifestMember(manifest: Json, key: ManifestKey): Json | undefined {
  if (typeof manifest !== "object" || manifest === null || Array.isArray(manifest)) return undefined;
  return manifest[key];
}
/** A manifest's field, or undefined where it has none or is no JSON. */
function manifestField(bytes: Buffer | null, field: ManifestKey): Json | undefined {
  if (bytes === null) return undefined;
  try {
    const parsed: Json = JSON.parse(bytes.toString("utf8"));
    return manifestMember(parsed, field);
  } catch {
    return undefined;
  }
}
/** Every string target in a JSON imports map is relative to its scope. */
function relativeImportTargets(value: Json | undefined): boolean {
  if (typeof value === "string") return value.startsWith("./");
  if (Array.isArray(value)) return value.every((target: Json) => relativeImportTargets(target));
  if (typeof value === "object" && value !== null)
    return Object.values(value).every((target: Json) => relativeImportTargets(target));
  return true;
}
/** The package scope of a module: the nearest `package.json` of its
 * directory or a directory above, read, as Node's loader finds it. */
function observeScope(module: string, checkLinks: boolean = false): { directory: string; bytes: Buffer | null } | null {
  for (const at of ancestors(dirname(module))) {
    if (basename(at) === "node_modules") break;
    const manifest = join(at, "package.json");
    if (kindOf(manifest, true) === "file") {
      realOf(at, true);
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
/** Whether Node resolves `specifier` to one of its built-in modules
 * (`node:fs`, `fs`), as `isBuiltin` of the running Node answers. */
export const builtinModule = (specifier: string): boolean => isBuiltin(specifier);

function observeResolution(specifier: string, parent: string): boolean {
  if (isBuiltin(specifier) || /^(node|data):/.test(specifier)) return false;
  // Another package lookup can resolve back into the scope through an
  // unobserved link, so completeness depends on the map's targets.
  if (specifier.startsWith("#")) {
    const scope = observeScope(parent, true);
    if (scope && !relativeImportTargets(manifestField(scope.bytes, "imports")))
      nodeUnobservable(`the package import ${specifier} has a non-relative target in its scope's imports`);
    return true;
  }
  if (/^(\.{0,2}\/|file:)/.test(specifier)) {
    let target: string;
    try {
      target = fileURLToPath(resolveHref(specifier, pathToFileHref(parent)));
    } catch {
      return false;
    }
    kindOf(target, true);
    realOf(target, true);
    return true;
  }
  const name = packageOf(specifier);
  // A self-reference resolves through its package scope's `exports`.
  const scope = observeScope(parent);
  if (scope && manifestField(scope.bytes, "name") === name && manifestField(scope.bytes, "exports") != null) {
    observeScope(parent, true);
    return true;
  }
  for (const at of ancestors(dirname(parent))) {
    const candidate = join(at, "node_modules", ...name.split("/"));
    if (kindOf(candidate, true) !== "directory") continue;
    realOf(candidate, true);
    observePackageLinks(candidate);
    if (manifestField(readAnswer(join(candidate, "package.json"), true).bytes, "exports") == null)
      nodeUnobservable(`the package ${name} of ${specifier} states no exports`);
    return true;
  }
  return false;
}

/** The module's location as `import.meta` holds it (`url`, `dirname`,
 * `filename`), checked to be a string (SOURCE-CONTRACTS.md, "Module
 * metadata"): `dirname` and `filename` are absent for a module not loaded
 * from a `file:` URL, and `url` is whatever the module's wrapper held. */
export function moduleLocation(value: unknown): string {
  if (typeof value !== "string") throw Error("import.meta holds no string location for this module");
  return value;
}

/** The URL Node's own ES module resolver resolves `specifier` to from the
 * module at `parent`, under the conditions it enables in this process: a
 * file URL with no query or fragment, else `null`, as where Node throws.
 * Run through a resolve hook, which calls Node's resolution with that parent
 * and resolves nothing else; it loads nothing. Its reads are observed before
 * and after it, and must agree; its target after it. A process cache
 * (`remembered`): resolved once, its observations made again at its first use
 * in each attempt (STAGE-STORE.md, "Shared work"). */
export function nodeResolve(specifier: string, parent: string): string | null {
  return remembered(resolutions, `${specifier}\0${parent}`, () => resolveObserved(specifier, parent));
}
/** Each resolution made in this process, with the observations it was made
 * from (`remembered`). */
const resolutions = new Map<string, Remembered<string | null>>();
/** Whether a serialized URL's query and fragment are empty or absent, as
 * its `search` and `hash` are `""`: nothing follows the first `#`, and
 * nothing follows the first `?` before it. */
function emptyQueryAndFragment(href: string): boolean {
  const fragment = href.indexOf("#");
  const beforeFragment = fragment < 0 ? href : href.slice(0, fragment);
  const query = beforeFragment.indexOf("?");
  return (fragment < 0 || fragment === href.length - 1) && (query < 0 || query === beforeFragment.length - 1);
}

function resolveObserved(specifier: string, parent: string): string | null {
  const before = observedNoting(() => fresh(() => observeResolution(specifier, parent)), false, false);
  // A parent with no file URL (a relative path with no working directory)
  // resolves nothing.
  let parentHref: string | null = null;
  try {
    parentHref = pathToFileHref(parent);
  } catch {
    parentHref = null;
  }
  const url = parentHref === null ? null : resolveWithNode(specifier, parentHref);
  const after = observedNoting(() => fresh(() => observeResolution(specifier, parent)), false, false);
  if (JSON.stringify(before.noted) !== JSON.stringify(after.noted))
    inconsistent(`the files Node read resolving ${specifier} from ${parent} changed meanwhile`);
  // The resolver answers a serialized URL: its scheme lowercase at the
  // start, so a `file:` prefix is its protocol, and `?` and `#` in its path
  // percent-encoded, so the first `#` starts its fragment and the first `?`
  // before it its query.
  const file = url !== null && url.startsWith("file:") ? url : null;
  if (file !== null) {
    const target = fileURLToPath(file);
    kindOf(target, true);
    realOf(target, true);
  } else if (after.value && !/^(\.{0,2}\/|file:)/.test(specifier))
    nodeUnobservable(`${specifier} is unresolved in the package found for it`);
  // A query or a fragment names another instance of the same file: refused.
  return file !== null && emptyQueryAndFragment(file) ? file : null;
}

/** The conditions Node's ES module resolution enables in this process
 * (`node`, `import`, `module-sync` and `node-addons` by default, and any
 * `--conditions`), read from the resolution itself through a resolve hook
 * (`resolutionConditions`), with `default`, which every resolution admits. */
let runtimeConditionsRead: readonly string[] | null = null;
export function runtimeConditions(): readonly string[] {
  if (runtimeConditionsRead) return runtimeConditionsRead;
  runtimeConditionsRead = [...resolutionConditions(), "default"];
  return runtimeConditionsRead;
}

/** The module at `path` of the installation at `root` (a real path), as
 * Node loads it (`loadObserved`): the bytes of each module the load reads,
 * as a load hook sees them, and its package scope are observed; a module
 * read outside the installation is not accounted for. What the load threw
 * is thrown once its reads are observed. Its own enumerable exports are
 * then copied to a fresh map by the boundary; a non-object gives null.
 * Copying runs accessors and Proxy traps and propagates their failures. */
export function loadModule(root: string, path: string): ReadonlyMap<string, unknown> | null {
  const { reads, outcome } = loadObserved(path);
  for (const { url, digest } of reads) {
    if (url === null) {
      nodeUnobservable(`loading ${path} read a module no URL names`);
      continue;
    }
    if (url.startsWith("node:")) continue;
    const file = url.startsWith("file:") ? fileURLToPath(url) : null;
    const real = file === null ? null : realOf(file, true);
    if (file === null || real === null || relative(root, real).split(sep)[0] === "..") {
      nodeUnobservable(`loading ${path} read ${url}, outside its installation`);
      continue;
    }
    observeScope(file);
    if (digest !== null) note("read", file, digest, true);
    else readAnswer(file, true);
  }
  if (outcome.k === "threw") throw outcome.thrown;
  return outcome.exports();
}
