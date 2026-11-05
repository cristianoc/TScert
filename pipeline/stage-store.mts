// The stage store's entries (STAGE-STORE.md, "Entries and timeouts"):
// finished results and timeout observations of replay-eligible stage
// invocations, each an immutable directory published by atomic rename, and
// the stable locations of source snapshots. The invocation mechanism
// (`stages.mts`) is the only user.
//
//   <root>/entries/<stage>/<key>/              a finished result
//       manifest.json   key, stage, input manifest, exit status, digests of
//                       stdout, stderr and each output, the measurement,
//                       and an integrity digest of the complete payload
//       stdout, stderr, out/<role>
//   <root>/timeouts/<stage>/<key>/<attempt>/observation.json
//   <root>/observed/<stage>/<pre-key>/<key>    a reference to an observed stage's entry
//   <root>/sources/<digest>/<name>             a stable snapshot location
//   <root>/tmp/<host>/<pid>.<attempt>/         a writer's unpublished entry
//   <root>/uses/<host>.<pid>.<id>            a process's uses: `<ms> <bytes> <item>` lines
//   <root>/uses/base                         the last eviction pass's items, one line each
//   <root>/evicting/<host>.<pid>.<id>          present while that process removes snapshots
//   <root>/eviction/owner                      the running pass or clean: host, process, id
import { appendFileSync, existsSync, lstatSync, mkdirSync, readdirSync, readFileSync, renameSync, rmdirSync, rmSync, statSync,
  writeFileSync } from "node:fs";
import { createHash, randomUUID } from "node:crypto";
import { hostname } from "node:os";
import { dirname, join } from "node:path";

const sha256 = (bytes: string | Buffer): string => createHash("sha256").update(bytes).digest("hex");

/** CPU time, with the processes it covers, and the largest peak memory in
 * bytes among the stage's processes the pipeline's own process aside, null
 * where there are none; or why nothing is measured. */
export type Cpu = { userMs: number; systemMs: number; peakBytes: number | null; covers: string } | { unavailable: string };

/** What an attempt measured: outside keys and result equality. */
export type Measurement = { attempt: string; elapsedMs: number; limitMs: number | null; cpu: Cpu };

/** A finished result: the exact input manifest it was computed from (the
 * canonical text whose digest is its key), its exit status, its standard
 * output and error, and its output files by role. */
export type StoredResult = {
  input: string;
  exitStatus: number | null;
  stdout: Buffer;
  stderr: Buffer;
  outputs: readonly (readonly [string, Buffer])[];
  measurement: Measurement;
};

/** A timeout observation: the stage key and input it was observed at, the
 * attempt, its elapsed time, its enforced limit, its resource policy and the
 * CPU time its processes used up to their kill. */
export type TimeoutObservation = {
  input: string;
  attempt: string;
  elapsedMs: number;
  limitMs: number;
  policy: string;
  cpu: Cpu;
};

/** A failure of the store's own consistency: two different results for
 * one key. */
export class StoreError extends Error {}

type Fields = { readonly [key: string]: unknown };
const fieldsOf = (value: unknown): Fields | null =>
  typeof value === "object" && value !== null && !Array.isArray(value) ? { ...value } : null;
const exactly = (fields: Fields, keys: readonly string[]): boolean =>
  Object.keys(fields).sort().join() === [...keys].sort().join();

function readCpu(value: unknown): Cpu | null {
  const c = fieldsOf(value);
  if (!c) return null;
  const { unavailable, userMs, systemMs, peakBytes, covers } = c;
  if (exactly(c, ["unavailable"]) && typeof unavailable === "string") return { unavailable };
  if (exactly(c, ["userMs", "systemMs", "peakBytes", "covers"]) && typeof userMs === "number" &&
      typeof systemMs === "number" && (peakBytes === null || typeof peakBytes === "number") && typeof covers === "string")
    return { userMs, systemMs, peakBytes, covers };
  return null;
}
export function readMeasurement(value: unknown): Measurement | null {
  const m = fieldsOf(value);
  if (!m || !exactly(m, ["attempt", "elapsedMs", "limitMs", "cpu"])) return null;
  const { attempt, elapsedMs, limitMs } = m;
  const cpu = readCpu(m["cpu"]);
  if (typeof attempt !== "string" || typeof elapsedMs !== "number" || !(limitMs === null || typeof limitMs === "number") ||
      !cpu)
    return null;
  return { attempt, elapsedMs, limitMs, cpu };
}

/** A file's digest and size, as a manifest states it. */
type Digest = { sha256: string; size: number };
const digestOf = (bytes: Buffer): Digest => ({ sha256: sha256(bytes), size: bytes.length });
function readDigest(value: unknown): Digest | null {
  const d = fieldsOf(value);
  if (!d || !exactly(d, ["sha256", "size"])) return null;
  const { sha256: digest, size } = d;
  return typeof digest === "string" && typeof size === "number" ? { sha256: digest, size } : null;
}
const matches = (bytes: Buffer, digest: Digest): boolean => bytes.length === digest.size && sha256(bytes) === digest.sha256;

/** An entry's manifest, decoded field by field. */
type ManifestPayload = {
  key: string;
  stage: string;
  input: string;
  exitStatus: number | null;
  stdout: Digest;
  stderr: Digest;
  outputs: { role: string; digest: Digest }[];
  measurement: Measurement;
};
type Manifest = ManifestPayload & { payloadSha256: string };
function readManifest(value: unknown): Manifest | null {
  const m = fieldsOf(value);
  if (!m || !exactly(m, ["key", "stage", "input", "exitStatus", "stdout", "stderr", "outputs", "measurement", "payloadSha256"])) return null;
  const { key, stage, input, exitStatus, outputs, payloadSha256 } = m;
  const stdout = readDigest(m["stdout"]), stderr = readDigest(m["stderr"]);
  const measurement = readMeasurement(m["measurement"]);
  if (typeof payloadSha256 !== "string" || typeof key !== "string" || typeof stage !== "string" || typeof input !== "string" ||
      !(exitStatus === null || typeof exitStatus === "number") || !stdout || !stderr || !measurement ||
      !Array.isArray(outputs))
    return null;
  const read: { role: string; digest: Digest }[] = [];
  for (const o of outputs) {
    const f = fieldsOf(o);
    const role = f?.["role"], digest = readDigest(f?.["digest"]);
    if (!f || !exactly(f, ["role", "digest"]) || typeof role !== "string" || !digest) return null;
    read.push({ role, digest });
  }
  const payload: ManifestPayload = { key, stage, input, exitStatus, stdout, stderr, outputs: read, measurement };
  return sha256(JSON.stringify(payload)) === payloadSha256 ? { ...payload, payloadSha256 } : null;
}

function readObservation(value: unknown): TimeoutObservation | null {
  const o = fieldsOf(value);
  if (!o || !exactly(o, ["input", "attempt", "elapsedMs", "limitMs", "policy", "cpu"])) return null;
  const { input, attempt, elapsedMs, limitMs, policy } = o;
  const cpu = readCpu(o["cpu"]);
  return typeof input === "string" && typeof attempt === "string" && typeof elapsedMs === "number" &&
    typeof limitMs === "number" && typeof policy === "string" && cpu
    ? { input, attempt, elapsedMs, limitMs, policy, cpu }
    : null;
}

/** Whether `error` is a file system error of one of `codes`. */
const failedWith = (error: unknown, ...codes: string[]): boolean =>
  error instanceof Error && "code" in error && typeof error.code === "string" && codes.includes(error.code);

/** The result payload two finished results for one key must agree on: the
 * input manifest, exit status, stdout, stderr and the outputs' names and
 * digests; attempt identities and measurements are excluded. */
const resultPayload = (m: Manifest): string =>
  JSON.stringify([m.input, m.exitStatus, m.stdout, m.stderr, m.outputs.map((o) => [o.role, o.digest])]);

/** An entry directory as read: its listing, its manifest's text and its
 * files' bytes. */
type EntryCopy = { listed: string; outs: string; manifest: string; stdout: Buffer; stderr: Buffer;
  outputs: ReadonlyMap<string, Buffer> };
/** The whole entry directory at `directory` read into memory, or null where
 * it is not an entry's shape; a file removed meanwhile throws. */
function readEntry(directory: string): EntryCopy | null {
  const listed = readdirSync(directory).sort().join();
  if (listed !== "manifest.json,out,stderr,stdout") return null;
  const roles = readdirSync(join(directory, "out")).sort();
  return {
    listed, outs: roles.join(), manifest: readFileSync(join(directory, "manifest.json"), "utf8"),
    stdout: readFileSync(join(directory, "stdout")), stderr: readFileSync(join(directory, "stderr")),
    outputs: new Map(roles.map((role) => [role, readFileSync(join(directory, "out", role))])),
  };
}
/** An entry copy's manifest where the whole copy is valid for `key` at
 * `input` (its manifest, its key, its input, every file's digest and no file
 * beyond them), else null. */
function validated(copy: EntryCopy, stage: string, key: string, input: string | null): Manifest | null {
  let manifest: Manifest | null;
  try {
    manifest = readManifest(JSON.parse(copy.manifest));
  } catch {
    return null;
  }
  if (!manifest || manifest.key !== key || manifest.stage !== stage || sha256(manifest.input) !== key ||
      (input !== null && manifest.input !== input))
    return null;
  if (copy.listed !== "manifest.json,out,stderr,stdout" || copy.outs !== manifest.outputs.map((o) => o.role).sort().join())
    return null;
  if (!matches(copy.stdout, manifest.stdout) || !matches(copy.stderr, manifest.stderr)) return null;
  for (const o of manifest.outputs) {
    const bytes = copy.outputs.get(o.role);
    if (bytes === undefined || !matches(bytes, o.digest)) return null;
  }
  return manifest;
}

// ---------------------------------------------------------------------------
// The use log and eviction (STAGE-STORE.md, "Location and size")

/** The bytes a file of `size` bytes takes on disk, in whole 4 KiB blocks. */
const blocks = (size: number): number => Math.ceil(size / 4096) * 4096;
/** An item of the store an eviction pass accounts: a finished entry, one
 * timeout observation, a source snapshot, or an observed stage's reference
 * (accounted with the entry it names). */
const itemShape = /^(?:entries\/[A-Za-z0-9_-]+\/[0-9a-f]{64}|timeouts\/[A-Za-z0-9_-]+\/[0-9a-f]{64}\/[A-Za-z0-9_.-]+|sources\/[0-9a-f]{64}|observed\/[A-Za-z0-9_-]+\/[0-9a-f]{64}\/[0-9a-f]{64})$/;
/** A use of an item, as a use line states it: when (ms since the epoch)
 * and the bytes it takes, 0 where the line does not measure it. */
type Use = { at: number; bytes: number };
/** The use lines of `text`, each a use of an item; a line of another
 * shape (a writer's partial last line) is skipped. */
function useLines(text: string, into: Map<string, Use>, held: Set<string> | null): void {
  for (const line of text.split("\n")) {
    const m = /^(\d+) (\d+) (\S+)$/.exec(line);
    if (!m || !itemShape.test(m[3] ?? "")) continue;
    const item = m[3] ?? "", at = Number(m[1]), bytes = Number(m[2]);
    const known = into.get(item);
    into.set(item, { at: Math.max(at, known?.at ?? 0), bytes: bytes || known?.bytes || 0 });
    if (item.startsWith("sources/")) held?.add(item);
  }
}
/** The use log of `root` this process appends to, and when it last
 * recorded each item's use. */
const useLogs = new Map<string, { file: string; recorded: Map<string, number> }>();
/** A use is recorded again after this long, so a pass orders items by when
 * they were last used to within it. */
const useResolutionMs = 10 * 60_000;
/** How often the orchestrators start an eviction pass at most. */
const evictionIntervalMs = 10 * 60_000;
/** A pass removes the least recently used items to this share of the budget. */
const lowWater = 0.8;
/** A synchronous pause of `ms` milliseconds. */
const pause = (ms: number): void => {
  Atomics.wait(new Int32Array(new SharedArrayBuffer(4)), 0, 0, ms);
};
/** The size of what `path` holds: each file's blocks, and the latest
 * modification time among it and its files. */
function measured(path: string): Use {
  const s = lstatSync(path);
  if (!s.isDirectory()) return { at: s.mtimeMs, bytes: blocks(s.size) };
  let at = s.mtimeMs, bytes = 0;
  for (const name of readdirSync(path)) {
    const inner = measured(join(path, name));
    at = Math.max(at, inner.at);
    bytes += inner.bytes;
  }
  return { at, bytes };
}
/** What an eviction pass did. */
export type EvictionPass = {
  elapsedMs: number;
  budgetBytes: number;
  /** The accounted bytes before and after the pass. */
  beforeBytes: number;
  afterBytes: number;
  items: number;
  /** Source snapshots a running process holds, which the pass keeps. */
  held: number;
  /** Items present that no use line names, measured by the pass. */
  measured: number;
  evicted: { entries: number; timeouts: number; sources: number; references: number };
};

/** An in-process test barrier after an entry is complete and before rename. */
let beforePublishForTests: ((directory: string) => void) | null = null;
export function pausePublicationForTests(hook: ((directory: string) => void) | null): void {
  beforePublishForTests = hook;
}

/** In-process test barriers of the eviction lock and of a removal of
 * snapshots: after a stale lock is judged and before it is moved
 * (`takeover`), before a moved lock naming another owner is renamed back
 * (`restore`), before the holder releases its lock (`release`), and after
 * a removal's marker is created, before (`marked`) and after (`reread`) the
 * use logs are read again. */
export type LockPoint = "takeover" | "restore" | "release" | "marked" | "reread";
let lockBarrierForTests: ((point: LockPoint) => void) | null = null;
export function pauseLockForTests(hook: ((point: LockPoint) => void) | null): void {
  lockBarrierForTests = hook;
}

export class Store {
  readonly root: string;
  /** Hosts whose owners a clean treats as stopped. */
  private forgotten: ReadonlySet<string> = new Set();
  constructor(root: string) {
    this.root = root;
  }
  private entry(stage: string, key: string): string {
    return join(this.root, "entries", stage, key);
  }
  private timeouts(stage: string, key: string): string {
    return join(this.root, "timeouts", stage, key);
  }
  /** A fresh directory for a writer's unpublished entry, named by its host
   * and process so a cleanup can tell whether its writer has stopped. */
  private temporary(attempt: string): string {
    const path = join(this.root, "tmp", hostname(), `${process.pid}.${attempt}`);
    mkdirSync(path, { recursive: true });
    return path;
  }
  /** Rename the complete directory or file `building` to `destination`,
   * creating its parent; a pass removing that parent meanwhile (an empty
   * reference or timeout directory) is retried. A destination present is the
   * caller's to judge. */
  private place(building: string, destination: string): void {
    for (let tries = 0; ; tries++) {
      mkdirSync(dirname(destination), { recursive: true });
      try {
        renameSync(building, destination);
        return;
      } catch (error) {
        if (!failedWith(error, "ENOENT") || tries >= 3 || !existsSync(building)) throw error;
      }
    }
  }
  /** Record a use of `item` (a path below the root) taking `bytes`, in this
   * process's use log: a publication always, a reuse once per
   * `useResolutionMs`. A source snapshot this process recorded is held
   * while it runs: no pass removes it. */
  private record(item: string, bytes: number, publication: boolean): void {
    let log = useLogs.get(this.root);
    if (!log) {
      log = { file: join(this.root, "uses", `${hostname()}.${process.pid}.${randomUUID().slice(0, 8)}`),
        recorded: new Map() };
      useLogs.set(this.root, log);
    }
    const now = Date.now();
    if (!publication && now - (log.recorded.get(item) ?? -Infinity) < useResolutionMs) return;
    const line = `${now} ${bytes} ${item}\n`;
    try {
      appendFileSync(log.file, line);
    } catch (error) {
      if (!failedWith(error, "ENOENT")) throw error;
      mkdirSync(dirname(log.file), { recursive: true });
      appendFileSync(log.file, line);
    }
    log.recorded.set(item, now);
  }

  /** The finished result stored for `key` at exactly `input`: the entry is
   * read whole into this process's memory, and that copy validated (its
   * manifest, its key, its input, every file's digest and no file beyond
   * them) and returned; a missing, incomplete, corrupt or concurrently
   * removed entry is a miss. */
  finished(stage: string, key: string, input: string | null): { result: StoredResult; lookupMs: number; validationMs: number } | null {
    const started = performance.now();
    let copy: EntryCopy | null;
    try {
      copy = readEntry(this.entry(stage, key));
    } catch (error) {
      if (failedWith(error, "ENOENT", "ENOTDIR", "EISDIR")) return null;
      throw error;
    }
    const copied = performance.now();
    const manifest = copy && validated(copy, stage, key, input);
    if (!copy || !manifest) return null;
    const outputs = manifest.outputs.map((o): readonly [string, Buffer] => [o.role, copy.outputs.get(o.role) ?? Buffer.alloc(0)]);
    this.record(`entries/${stage}/${key}`, blocks(Buffer.byteLength(copy.manifest)) + blocks(copy.stdout.length) +
      blocks(copy.stderr.length) + outputs.reduce((sum, [, bytes]) => sum + blocks(bytes.length), 0), false);
    return {
      result: {
        input: manifest.input, exitStatus: manifest.exitStatus, stdout: copy.stdout, stderr: copy.stderr, outputs,
        measurement: manifest.measurement,
      },
      lookupMs: copied - started,
      validationMs: performance.now() - copied,
    };
  }
  /** The entry directory's manifest where the whole entry is valid for `key`
   * at `input`, else null. */
  private validatedAt(directory: string, stage: string, key: string, input: string | null): Manifest | null {
    try {
      const copy = readEntry(directory);
      return copy && validated(copy, stage, key, input);
    } catch (error) {
      if (failedWith(error, "ENOENT", "ENOTDIR", "EISDIR")) return null;
      throw error;
    }
  }

  /** Publish a finished result for `key`: built whole in a temporary
   * directory, then renamed to its destination. Where an entry is there
   * already, it is validated: a valid entry with another payload is a store
   * error; an invalid one is left, and the fresh result is not published. */
  publishFinished(stage: string, key: string, result: StoredResult): "published" | "present" | "invalid present" {
    if (sha256(result.input) !== key) throw new StoreError(`store error: the input of ${stage} entry ${key} is not its key's`);
    const payload: ManifestPayload = {
      key, stage, input: result.input, exitStatus: result.exitStatus,
      stdout: digestOf(result.stdout), stderr: digestOf(result.stderr),
      outputs: result.outputs.map(([role, bytes]) => ({ role, digest: digestOf(bytes) })),
      measurement: result.measurement,
    };
    const manifest: Manifest = { ...payload, payloadSha256: sha256(JSON.stringify(payload)) };
    const building = this.temporary(result.measurement.attempt);
    try {
      mkdirSync(join(building, "out"));
      for (const [role, bytes] of result.outputs) writeFileSync(join(building, "out", role), bytes, { mode: 0o444 });
      writeFileSync(join(building, "stdout"), result.stdout, { mode: 0o444 });
      writeFileSync(join(building, "stderr"), result.stderr, { mode: 0o444 });
      const manifestText = JSON.stringify(manifest);
      writeFileSync(join(building, "manifest.json"), manifestText, { mode: 0o444 });
      const destination = this.entry(stage, key);
      // Recorded before it is visible, so every entry no use line names is one
      // a pass can measure.
      this.record(`entries/${stage}/${key}`, blocks(Buffer.byteLength(manifestText)) + blocks(result.stdout.length) +
        blocks(result.stderr.length) + result.outputs.reduce((sum, [, bytes]) => sum + blocks(bytes.length), 0), true);
      beforePublishForTests?.(building);
      try {
        this.place(building, destination);
        return "published";
      } catch (error) {
        if (!failedWith(error, "EEXIST", "ENOTEMPTY")) throw error;
      }
      const present = this.validatedAt(destination, stage, key, null);
      if (!present) return "invalid present";
      if (resultPayload(present) !== resultPayload(manifest))
        throw new StoreError(`store error: two different results for ${stage} entry ${key} (attempts ` +
          `${present.measurement.attempt} and ${result.measurement.attempt})`);
      return "present";
    } finally {
      rmSync(building, { recursive: true, force: true });
    }
  }

  /** A timeout observation of `key` at exactly `input` under `policy` whose
   * enforced limit is at least `limitMs`, or null. */
  timeout(stage: string, key: string, input: string, limitMs: number, policy: string):
      { observation: TimeoutObservation; lookupMs: number } | null {
    const started = performance.now();
    let attempts: string[];
    try {
      attempts = readdirSync(this.timeouts(stage, key)).sort();
    } catch (error) {
      if (failedWith(error, "ENOENT", "ENOTDIR")) return null;
      throw error;
    }
    for (const attempt of attempts) {
      let observation: TimeoutObservation | null, text: string;
      try {
        text = readFileSync(join(this.timeouts(stage, key), attempt, "observation.json"), "utf8");
        observation = readObservation(JSON.parse(text));
      } catch {
        continue;
      }
      if (observation && observation.attempt === attempt && sha256(observation.input) === key &&
          observation.input === input && observation.policy === policy && observation.limitMs >= limitMs) {
        this.record(`timeouts/${stage}/${key}/${attempt}`, blocks(Buffer.byteLength(text)), false);
        return { observation, lookupMs: performance.now() - started };
      }
    }
    return null;
  }

  /** The keys referenced under an observed stage's pre-key, newest first:
   * candidates only, each entry validated by its reader. */
  candidates(stage: string, preKey: string): string[] {
    const directory = join(this.root, "observed", stage, preKey);
    let names: string[];
    try {
      names = readdirSync(directory);
    } catch (error) {
      if (failedWith(error, "ENOENT", "ENOTDIR")) return [];
      throw error;
    }
    const time = (name: string): number => {
      try {
        return statSync(join(directory, name)).mtimeMs;
      } catch {
        return 0;
      }
    };
    return names.filter((n) => /^[0-9a-f]{64}$/.test(n)).map((n) => ({ n, t: time(n) }))
      .sort((a, b) => b.t - a.t || (a.n < b.n ? -1 : 1)).map((c) => c.n);
  }
  /** Reference the published entry `key` under its pre-key: an empty file,
   * written once. */
  reference(stage: string, preKey: string, key: string): void {
    const directory = join(this.root, "observed", stage, preKey);
    this.record(`observed/${stage}/${preKey}/${key}`, 0, true);
    for (let tries = 0; ; tries++) {
      mkdirSync(directory, { recursive: true });
      try {
        writeFileSync(join(directory, key), "", { flag: "wx", mode: 0o444 });
        return;
      } catch (error) {
        if (failedWith(error, "EEXIST")) return;
        // A pass removed the empty pre-key directory meanwhile.
        if (!failedWith(error, "ENOENT") || tries >= 3) throw error;
      }
    }
  }

  /** Publish a timeout observation at its attempt's own destination. */
  publishTimeout(stage: string, key: string, observation: TimeoutObservation): void {
    const building = this.temporary(observation.attempt);
    try {
      const text = JSON.stringify(observation);
      writeFileSync(join(building, "observation.json"), text, { mode: 0o444 });
      const destination = join(this.timeouts(stage, key), observation.attempt);
      this.record(`timeouts/${stage}/${key}/${observation.attempt}`, blocks(Buffer.byteLength(text)), true);
      beforePublishForTests?.(building);
      this.place(building, destination);
    } finally {
      rmSync(building, { recursive: true, force: true });
    }
  }

  /** A stable, content-addressed directory holding exactly `files` (each a
   * name and its bytes), published once and validated at each use; null
   * where the directory present is not exactly those files, or where a
   * running process is removing snapshots. The use is recorded before that
   * check, so the directory is held from then on while this process runs. */
  stableDirectory(category: string, files: readonly (readonly [string, Buffer])[]): string | null {
    const digest = sha256(JSON.stringify(files.map(([name, bytes]) => [name, sha256(bytes)])));
    const destination = join(this.root, category, digest);
    this.record(`${category}/${digest}`, files.reduce((sum, [, bytes]) => sum + blocks(bytes.length), 0), true);
    if (this.removingSnapshots()) return null;
    const valid = (): boolean => {
      try {
        if (readdirSync(destination).sort().join("\n") !== files.map(([name]) => name).sort().join("\n")) return false;
        return files.every(([name, bytes]) => readFileSync(join(destination, name)).equals(bytes));
      } catch (error) {
        if (failedWith(error, "ENOENT", "ENOTDIR")) return false;
        throw error;
      }
    };
    if (valid()) return destination;
    const building = this.temporary(`${category}-${digest}`);
    try {
      for (const [name, bytes] of files) writeFileSync(join(building, name), bytes, { mode: 0o444 });
      try {
        this.place(building, destination);
      } catch (error) {
        if (!failedWith(error, "EEXIST", "ENOTEMPTY")) throw error;
      }
    } finally {
      rmSync(building, { recursive: true, force: true });
    }
    return valid() ? destination : null;
  }

  /** Whether a running process is removing snapshots: a marker of it is in
   * `evicting/`. */
  private removingSnapshots(): boolean {
    return this.names("evicting").some((name) => this.running(name));
  }
  /** Whether the owner `<host> <pid> <id>` (or `<host>.<pid>.<id>`, a file
   * name) is running: a process of this host that is alive, or any owner of
   * another host, whose processes this host cannot see, unless a clean of
   * this host names that host as forgotten. An owner of neither shape is not
   * running. */
  private running(owner: string): boolean {
    const m = /^(.+)[ .](\d+)[ .][0-9a-f]{8}$/.exec(owner);
    if (!m) return false;
    const host = m[1] ?? "";
    return host === hostname() ? alive(Number(m[2])) : !this.forgotten.has(host);
  }
  /** The owner named by the lock directory `path`: null where it has no
   * readable owner file; undefined where there is no directory. */
  private ownerAt(path: string): string | null | undefined {
    try {
      return readFileSync(join(path, "owner"), "utf8");
    } catch (error) {
      if (!failedWith(error, "ENOENT", "ENOTDIR")) throw error;
      return existsSync(path) ? null : undefined;
    }
  }

  /** Whether a pass is due: no running process holds the lock, and the last
   * pass finished more than `evictionIntervalMs` ago or none has. */
  evictionDue(): boolean {
    const owner = this.ownerAt(join(this.root, "eviction"));
    if (typeof owner === "string" && this.running(owner)) return false;
    try {
      return Date.now() - statSync(join(this.root, "uses", "base")).mtimeMs > evictionIntervalMs;
    } catch (error) {
      if (failedWith(error, "ENOENT")) return existsSync(this.root);
      throw error;
    }
  }
  /** Move the lock at `lock` into this process's temporary directory and
   * delete it there where it names `expected` (null: no owner file); where
   * it names another, rename it back, and where a new lock took its place
   * meanwhile, leave it in the temporary directory, which goes when this
   * process has stopped. */
  private moveLock(lock: string, expected: string | null): void {
    const moved = join(this.root, "tmp", hostname(), `${process.pid}.lock-moved-${randomUUID().slice(0, 8)}`);
    mkdirSync(dirname(moved), { recursive: true });
    try {
      renameSync(lock, moved);
    } catch (error) {
      if (failedWith(error, "ENOENT")) return;
      throw error;
    }
    if (this.ownerAt(moved) === expected) {
      rmSync(moved, { recursive: true, force: true });
      return;
    }
    lockBarrierForTests?.("restore");
    try {
      renameSync(moved, lock);
    } catch (error) {
      if (!failedWith(error, "EEXIST", "ENOTEMPTY")) throw error;
    }
  }
  /** Run `body` holding the store's eviction lock; null where a running
   * process holds it and `wait` is false. The lock is the directory
   * `eviction/`, built whole with its owner file (host, process, a random
   * id) in a temporary directory and renamed into place, so a lock present
   * names its owner. A lock whose owner has stopped, or one without an owner
   * file, is taken over by `moveLock`, as the holder releases its own. The
   * lock keeps passes from repeating each other's work; two passes at once
   * remove nothing a running process holds either (each snapshot removal
   * has a marker of its own). */
  private locked<T>(wait: boolean, body: () => T): T | null {
    const lock = join(this.root, "eviction");
    const owner = `${hostname()} ${process.pid} ${randomUUID().slice(0, 8)}`;
    mkdirSync(this.root, { recursive: true });
    for (;;) {
      const building = this.temporary(`lock-${randomUUID().slice(0, 8)}`);
      writeFileSync(join(building, "owner"), owner);
      try {
        renameSync(building, lock);
        break;
      } catch (error) {
        rmSync(building, { recursive: true, force: true });
        if (!failedWith(error, "EEXIST", "ENOTEMPTY")) throw error;
      }
      const held = this.ownerAt(lock);
      if (held === undefined) continue;
      if (held === null || !this.running(held)) {
        lockBarrierForTests?.("takeover");
        this.moveLock(lock, held);
        continue;
      }
      if (!wait) return null;
      pause(200);
    }
    try {
      return body();
    } finally {
      lockBarrierForTests?.("release");
      this.moveLock(lock, owner);
    }
  }

  /** Every item the use logs name, with when it was last used and its
   * bytes; the snapshots running processes recorded (held); whether a base is
   * there; and the files of the processes that have stopped, which the base,
   * once rewritten, replaces. */
  private readUses(): { items: Map<string, Use>; held: Set<string>; stopped: string[]; based: boolean } {
    const directory = join(this.root, "uses");
    const items = new Map<string, Use>(), held = new Set<string>(), stopped: string[] = [];
    let based = true;
    try {
      useLines(readFileSync(join(directory, "base"), "utf8"), items, null);
    } catch (error) {
      if (!failedWith(error, "ENOENT")) throw error;
      based = false;
    }
    let names: string[];
    try {
      names = readdirSync(directory);
    } catch (error) {
      if (failedWith(error, "ENOENT")) return { items, held, stopped, based };
      throw error;
    }
    for (const name of names) {
      if (!/^(.+)\.(\d+)\.[0-9a-f]{8}$/.test(name)) continue;
      const running = this.running(name);
      let text: string;
      try {
        text = readFileSync(join(directory, name), "utf8");
      } catch (error) {
        if (failedWith(error, "ENOENT")) continue;
        throw error;
      }
      useLines(text, items, running ? held : null);
      if (!running) stopped.push(name);
    }
    return { items, held, stopped, based };
  }
  /** The names in the directory `path` of the store, none where it is
   * absent. */
  private names(path: string): string[] {
    try {
      return readdirSync(join(this.root, path));
    } catch (error) {
      if (failedWith(error, "ENOENT", "ENOTDIR")) return [];
      throw error;
    }
  }
  /** The items of `part` present: `entries/<stage>/<key>`,
   * `timeouts/<stage>/<key>/<attempt>` or `sources/<digest>`. */
  private present(part: "entries" | "timeouts" | "sources"): string[] {
    const below = (paths: string[]): string[] => paths.flatMap((path) => this.names(path).map((n) => `${path}/${n}`));
    const found = part === "sources" ? below([part]) : part === "entries" ? below(below([part])) : below(below(below([part])));
    return found.filter((i) => itemShape.test(i));
  }
  /** Move `items` out of the store into `holding`, one of this process's
   * temporaries, then remove it: a reader sees each item whole or absent.
   * Returns the items moved. */
  private evict(items: readonly string[], holding: string): string[] {
    if (!items.length) return [];
    mkdirSync(holding, { recursive: true });
    const moved: string[] = [];
    try {
      for (const [i, item] of items.entries()) {
        try {
          renameSync(join(this.root, item), join(holding, String(i)));
          moved.push(item);
        } catch (error) {
          if (!failedWith(error, "ENOENT")) throw error;
        }
      }
    } finally {
      rmSync(holding, { recursive: true, force: true });
    }
    return moved;
  }
  /** Remove the source snapshots `candidates` no running process holds,
   * under a marker of this process, which `stableDirectory` checks: the
   * holds are read again after the marker is created, so a use recorded
   * before that read is seen, and one recorded after it sees the marker and
   * does without the store's snapshot. */
  private evictSources(candidates: readonly string[], holding: string): string[] {
    if (!candidates.length) return [];
    const marker = join(this.root, "evicting", `${hostname()}.${process.pid}.${randomUUID().slice(0, 8)}`);
    mkdirSync(dirname(marker), { recursive: true });
    writeFileSync(marker, "", { flag: "wx" });
    mkdirSync(holding, { recursive: true });
    const moved: string[] = [];
    try {
      lockBarrierForTests?.("marked");
      const { held } = this.readUses();
      lockBarrierForTests?.("reread");
      for (const [i, item] of candidates.entries()) {
        if (held.has(item)) continue;
        try {
          renameSync(join(this.root, item), join(holding, String(i)));
          moved.push(item);
        } catch (error) {
          if (!failedWith(error, "ENOENT")) throw error;
        }
      }
    } finally {
      rmSync(marker, { force: true });
      rmSync(holding, { recursive: true, force: true });
    }
    return moved;
  }
  /** Write the pass summary, uses/base: `items`, one line each, then remove the files
   * of the stopped processes it folds in. */
  private writeBase(items: ReadonlyMap<string, Use>, stopped: readonly string[]): void {
    const directory = join(this.root, "uses");
    mkdirSync(directory, { recursive: true });
    const lines: string[] = [];
    for (const [item, use] of items) lines.push(`${Math.round(use.at)} ${use.bytes} ${item}\n`);
    const building = this.temporary("base");
    try {
      writeFileSync(join(building, "base"), lines.join(""));
      renameSync(join(building, "base"), join(directory, "base"));
    } finally {
      rmSync(building, { recursive: true, force: true });
    }
    for (const name of stopped) if (!this.running(name)) rmSync(join(directory, name), { force: true });
  }

  /** One eviction pass, unless another is running: the use logs' items,
   * reconciled with the items present (an item present that no use line
   * names is measured; one recorded and absent is dropped), and where they
   * take more than `budgetBytes`, the least recently used items no running
   * process holds removed until they take at most `lowWater` of it, an
   * entry with its references. Without a base, the references present are
   * listed too. */
  evictionPass(budgetBytes: number): EvictionPass | null {
    return this.locked(false, () => {
      const started = performance.now();
      const { items, held, stopped, based } = this.readUses();
      const present = new Set([...this.present("entries"), ...this.present("timeouts"), ...this.present("sources")]);
      let measuredCount = 0;
      for (const item of present) {
        if (items.has(item)) continue;
        try {
          items.set(item, measured(join(this.root, item)));
          measuredCount++;
        } catch (error) {
          if (!failedWith(error, "ENOENT", "ENOTDIR")) throw error;
        }
      }
      if (!based)
        for (const stage of this.names("observed"))
          for (const preKey of this.names(`observed/${stage}`))
            for (const key of this.names(`observed/${stage}/${preKey}`)) {
              const item = `observed/${stage}/${preKey}/${key}`;
              if (itemShape.test(item) && !items.has(item)) items.set(item, { at: 0, bytes: 0 });
            }
      const evicted = { entries: 0, timeouts: 0, sources: 0, references: 0 };
      const unreference = (item: string): void => {
        items.delete(item);
        try {
          rmSync(join(this.root, item), { force: true });
          rmdirSync(dirname(join(this.root, item)));
        } catch (error) {
          if (!failedWith(error, "ENOENT", "ENOTEMPTY", "EEXIST")) throw error;
        }
      };
      // An entry's references, by the entry; a reference to no entry present
      // is removed.
      const references = new Map<string, string[]>();
      for (const item of [...items.keys()]) {
        const [part, stage, preKey, key] = item.split("/");
        if (part !== "observed") {
          if (!present.has(item)) items.delete(item);
          continue;
        }
        const entry = `entries/${stage}/${key}`;
        if (!present.has(entry)) unreference(item);
        else references.set(entry, [...(references.get(entry) ?? []), `observed/${stage}/${preKey}/${key}`]);
      }
      let total = 0;
      for (const [item, use] of items) total += use.bytes;
      const before = total;
      if (total > budgetBytes) {
        const order = [...items].filter(([item]) => !item.startsWith("observed/") && !held.has(item))
          .sort(([a, x], [b, y]) => x.at - y.at || (a < b ? -1 : 1));
        const chosen: string[] = [];
        let remaining = total;
        for (const [item, use] of order) {
          if (remaining <= budgetBytes * lowWater) break;
          chosen.push(item);
          remaining -= use.bytes;
        }
        const holding = join(this.root, "tmp", hostname(), `${process.pid}.evict`);
        const removed = [...this.evict(chosen.filter((c) => !c.startsWith("sources/")), holding),
          ...this.evictSources(chosen.filter((c) => c.startsWith("sources/")), holding)];
        for (const item of removed) {
          total -= items.get(item)?.bytes ?? 0;
          items.delete(item);
          if (item.startsWith("entries/")) evicted.entries++;
          else if (item.startsWith("timeouts/")) {
            evicted.timeouts++;
            try {
              rmdirSync(dirname(join(this.root, item)));
            } catch (error) {
              if (!failedWith(error, "ENOENT", "ENOTEMPTY", "EEXIST")) throw error;
            }
          }
          else evicted.sources++;
          for (const reference of references.get(item) ?? []) {
            unreference(reference);
            evicted.references++;
          }
        }
      }
      this.removeStoppedTemporaries();
      this.writeBase(items, stopped);
      return {
        elapsedMs: performance.now() - started, budgetBytes, beforeBytes: before, afterBytes: total,
        items: [...items.keys()].filter((i) => !i.startsWith("observed/")).length, held: held.size,
        measured: measuredCount, evicted,
      };
    });
  }

  /** Remove every stored entry, timeout observation and reference, every
   * source snapshot no running process holds, and each temporary directory
   * whose writer has stopped: one of this host whose process is gone. Waits
   * for a running pass. The owners of the hosts `forgetHosts` count as
   * stopped: their locks, markers and use logs go, and so do the snapshots
   * they hold. */
  clean(forgetHosts: readonly string[] = []): void {
    this.forgotten = new Set(forgetHosts);
    try {
      this.cleanLocked();
    } finally {
      this.forgotten = new Set();
    }
  }
  private cleanLocked(): void {
    this.locked(true, () => {
      for (const part of ["entries", "timeouts", "observed"]) rmSync(join(this.root, part), { recursive: true, force: true });
      this.evictSources(this.present("sources"), join(this.root, "tmp", hostname(), `${process.pid}.clean`));
      this.removeStoppedTemporaries();
      const { stopped } = this.readUses();
      rmSync(join(this.root, "uses", "base"), { force: true });
      for (const name of stopped) rmSync(join(this.root, "uses", name), { force: true });
      for (const name of this.names("evicting")) if (!this.running(name)) rmSync(join(this.root, "evicting", name), { force: true });
    });
  }
  /** Remove each temporary directory of this host whose process is gone. */
  private removeStoppedTemporaries(): void {
    const here = join(this.root, "tmp", hostname());
    let temporaries: string[];
    try {
      temporaries = readdirSync(here);
    } catch (error) {
      if (failedWith(error, "ENOENT")) return;
      throw error;
    }
    for (const name of temporaries)
      if (!alive(Number(name.split(".")[0]))) rmSync(join(here, name), { recursive: true, force: true });
  }
}

/** Whether a process of this host is running: anything but a process
 * reported absent counts as running. */
function alive(pid: number): boolean {
  if (!Number.isSafeInteger(pid) || pid <= 0) return true;
  try {
    process.kill(pid, 0);
    return true;
  } catch (error) {
    return !failedWith(error, "ESRCH");
  }
}
