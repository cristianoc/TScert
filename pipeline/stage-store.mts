// The stage store's entries (DESIGN.md, "The stage store"): finished results
// and timeout observations of replay-eligible stage invocations, each an
// immutable directory published by atomic rename, and the stable locations
// of source snapshots. The invocation mechanism (`stages.mts`) is the only
// user.
//
//   <root>/entries/<stage>/<key>/              a finished result
//       manifest.json   key, stage, input manifest, exit status, digests of
//                       stdout, stderr and each output, and the measurement
//       stdout, stderr, out/<role>
//   <root>/timeouts/<stage>/<key>/<attempt>/observation.json
//   <root>/sources/<digest>/<name>             a stable snapshot location
//   <root>/tmp/<host>/<pid>.<attempt>/         a writer's unpublished entry
import { cpSync, mkdirSync, readdirSync, readFileSync, renameSync, rmSync, writeFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { hostname } from "node:os";
import { dirname, join } from "node:path";
import { runDirectory } from "./run-directory.mts";

const sha256 = (bytes: string | Buffer): string => createHash("sha256").update(bytes).digest("hex");

/** CPU time, with the processes it covers, or why none is measured. */
export type Cpu = { userMs: number; systemMs: number; covers: string } | { unavailable: string };

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
 * attempt, its elapsed time, its enforced limit and its resource policy. */
export type TimeoutObservation = {
  input: string;
  attempt: string;
  elapsedMs: number;
  limitMs: number;
  policy: string;
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
  const { unavailable, userMs, systemMs, covers } = c;
  if (exactly(c, ["unavailable"]) && typeof unavailable === "string") return { unavailable };
  if (exactly(c, ["userMs", "systemMs", "covers"]) && typeof userMs === "number" && typeof systemMs === "number" &&
      typeof covers === "string")
    return { userMs, systemMs, covers };
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
type Manifest = {
  key: string;
  stage: string;
  input: string;
  exitStatus: number | null;
  stdout: Digest;
  stderr: Digest;
  outputs: { role: string; digest: Digest }[];
  measurement: Measurement;
};
function readManifest(value: unknown): Manifest | null {
  const m = fieldsOf(value);
  if (!m || !exactly(m, ["key", "stage", "input", "exitStatus", "stdout", "stderr", "outputs", "measurement"])) return null;
  const { key, stage, input, exitStatus, outputs } = m;
  const stdout = readDigest(m["stdout"]), stderr = readDigest(m["stderr"]);
  const measurement = readMeasurement(m["measurement"]);
  if (typeof key !== "string" || typeof stage !== "string" || typeof input !== "string" ||
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
  return { key, stage, input, exitStatus, stdout, stderr, outputs: read, measurement };
}

function readObservation(value: unknown): TimeoutObservation | null {
  const o = fieldsOf(value);
  if (!o || !exactly(o, ["input", "attempt", "elapsedMs", "limitMs", "policy"])) return null;
  const { input, attempt, elapsedMs, limitMs, policy } = o;
  return typeof input === "string" && typeof attempt === "string" && typeof elapsedMs === "number" &&
    typeof limitMs === "number" && typeof policy === "string"
    ? { input, attempt, elapsedMs, limitMs, policy }
    : null;
}

/** Whether `error` is a file system error of one of `codes`. */
const failedWith = (error: unknown, ...codes: string[]): boolean =>
  error instanceof Error && "code" in error && typeof error.code === "string" && codes.includes(error.code);

/** The result payload two finished results for one key must agree on: the
 * input manifest, exit status, stdout, stderr and the outputs' names and
 * digests; attempt identities and measurements are excluded. */
const payload = (m: Manifest): string =>
  JSON.stringify([m.input, m.exitStatus, m.stdout, m.stderr, m.outputs.map((o) => [o.role, o.digest])]);

export class Store {
  readonly root: string;
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

  /** The finished result stored for `key` at exactly `input`: the entry is
   * copied whole into this run's directory and validated there (its
   * manifest, its key, its input, every file's digest and no file beyond
   * them); a missing, incomplete, corrupt or concurrently removed entry is a
   * miss. */
  finished(stage: string, key: string, input: string): { result: StoredResult; lookupMs: number; validationMs: number } | null {
    const started = performance.now();
    const copy = join(runDirectory(`stage-entry-${stage}-`), "entry");
    try {
      cpSync(this.entry(stage, key), copy, { recursive: true });
    } catch (error) {
      if (failedWith(error, "ENOENT", "ENOTDIR")) return null;
      throw error;
    }
    const copied = performance.now();
    try {
      const manifest = this.validated(copy, stage, key, input);
      if (!manifest) return null;
      const outputs = manifest.outputs.map((o): readonly [string, Buffer] => [o.role, readFileSync(join(copy, "out", o.role))]);
      return {
        result: {
          input: manifest.input, exitStatus: manifest.exitStatus,
          stdout: readFileSync(join(copy, "stdout")), stderr: readFileSync(join(copy, "stderr")), outputs,
          measurement: manifest.measurement,
        },
        lookupMs: copied - started,
        validationMs: performance.now() - copied,
      };
    } finally {
      rmSync(dirname(copy), { recursive: true, force: true });
    }
  }
  /** An entry directory's manifest where the whole entry is valid for
   * `key` at `input`, else null. */
  private validated(directory: string, stage: string, key: string, input: string | null): Manifest | null {
    let manifest: Manifest | null;
    try {
      manifest = readManifest(JSON.parse(readFileSync(join(directory, "manifest.json"), "utf8")));
    } catch {
      return null;
    }
    if (!manifest || manifest.key !== key || manifest.stage !== stage || sha256(manifest.input) !== key ||
        (input !== null && manifest.input !== input))
      return null;
    try {
      const listed = readdirSync(directory).sort().join();
      const outs = readdirSync(join(directory, "out")).sort().join();
      if (listed !== "manifest.json,out,stderr,stdout" || outs !== manifest.outputs.map((o) => o.role).sort().join())
        return null;
      if (!matches(readFileSync(join(directory, "stdout")), manifest.stdout) ||
          !matches(readFileSync(join(directory, "stderr")), manifest.stderr))
        return null;
      for (const o of manifest.outputs)
        if (!matches(readFileSync(join(directory, "out", o.role)), o.digest)) return null;
    } catch (error) {
      if (failedWith(error, "ENOENT", "ENOTDIR", "EISDIR")) return null;
      throw error;
    }
    return manifest;
  }

  /** Publish a finished result for `key`: built whole in a temporary
   * directory, then renamed to its destination. Where an entry is there
   * already, it is validated: a valid entry with another payload is a store
   * error; an invalid one is left, and the fresh result is not published. */
  publishFinished(stage: string, key: string, result: StoredResult): "published" | "present" | "invalid present" {
    if (sha256(result.input) !== key) throw new StoreError(`store error: the input of ${stage} entry ${key} is not its key's`);
    const manifest: Manifest = {
      key, stage, input: result.input, exitStatus: result.exitStatus,
      stdout: digestOf(result.stdout), stderr: digestOf(result.stderr),
      outputs: result.outputs.map(([role, bytes]) => ({ role, digest: digestOf(bytes) })),
      measurement: result.measurement,
    };
    const building = this.temporary(result.measurement.attempt);
    try {
      mkdirSync(join(building, "out"));
      for (const [role, bytes] of result.outputs) writeFileSync(join(building, "out", role), bytes, { mode: 0o444 });
      writeFileSync(join(building, "stdout"), result.stdout, { mode: 0o444 });
      writeFileSync(join(building, "stderr"), result.stderr, { mode: 0o444 });
      writeFileSync(join(building, "manifest.json"), JSON.stringify(manifest), { mode: 0o444 });
      const destination = this.entry(stage, key);
      mkdirSync(dirname(destination), { recursive: true });
      try {
        renameSync(building, destination);
        return "published";
      } catch (error) {
        if (!failedWith(error, "EEXIST", "ENOTEMPTY")) throw error;
      }
      const present = this.validated(destination, stage, key, null);
      if (!present) return "invalid present";
      if (payload(present) !== payload(manifest))
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
      let observation: TimeoutObservation | null;
      try {
        observation = readObservation(JSON.parse(readFileSync(join(this.timeouts(stage, key), attempt, "observation.json"),
          "utf8")));
      } catch {
        continue;
      }
      if (observation && observation.attempt === attempt && sha256(observation.input) === key &&
          observation.input === input && observation.policy === policy && observation.limitMs >= limitMs)
        return { observation, lookupMs: performance.now() - started };
    }
    return null;
  }

  /** Publish a timeout observation at its attempt's own destination. */
  publishTimeout(stage: string, key: string, observation: TimeoutObservation): void {
    const building = this.temporary(observation.attempt);
    try {
      writeFileSync(join(building, "observation.json"), JSON.stringify(observation), { mode: 0o444 });
      const destination = join(this.timeouts(stage, key), observation.attempt);
      mkdirSync(dirname(destination), { recursive: true });
      renameSync(building, destination);
    } finally {
      rmSync(building, { recursive: true, force: true });
    }
  }

  /** A stable, content-addressed directory holding exactly `files` (each a
   * name and its bytes), published once and validated at each use; null
   * where the directory present is not exactly those files. */
  stableDirectory(category: string, files: readonly (readonly [string, Buffer])[]): string | null {
    const digest = sha256(JSON.stringify(files.map(([name, bytes]) => [name, sha256(bytes)])));
    const destination = join(this.root, category, digest);
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
      mkdirSync(dirname(destination), { recursive: true });
      try {
        renameSync(building, destination);
      } catch (error) {
        if (!failedWith(error, "EEXIST", "ENOTEMPTY")) throw error;
      }
    } finally {
      rmSync(building, { recursive: true, force: true });
    }
    return valid() ? destination : null;
  }

  /** Remove every stored entry, observation and stable location, and each
   * temporary directory whose writer has stopped: one of this host whose
   * process is gone. */
  clean(): void {
    for (const part of ["entries", "timeouts", "sources"]) rmSync(join(this.root, part), { recursive: true, force: true });
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
