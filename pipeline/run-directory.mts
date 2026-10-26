// Temporary directories of one invocation. Every directory a run, a check or
// a test writes lies under one root per process tree: the first process to
// ask creates it, the processes it forks inherit it through the environment,
// and the creating process removes it when it exits. A command that prints a
// run's directory for inspection keeps the root instead: the newest `keptRoots`
// kept roots stay, and each new kept root removes the older ones. A root whose
// creating process died without removing it (a kill it could not handle) is
// removed by the next process that creates a root.

import { mkdtempSync, readdirSync, readFileSync, rmSync, statSync, statfsSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const variable = "TSCERT_RUN_ROOT";
const prefix = "tscert-runs-";
const owner = ".owner";
const keptMark = ".kept";
/** How many kept roots stay for inspection. */
export const keptRoots: number = 20;
let kept: boolean = false;

/** Whether the process `pid` is alive: signal 0 tests existence only. */
function alive(pid: number): boolean {
  try {
    process.kill(pid, 0);
    return true;
  } catch (error) {
    return error instanceof Error && "code" in error && error.code === "EPERM";
  }
}

type Root = { path: string; pid: number | null; kept: boolean; mtimeMs: number };

/** The roots under the temporary directory, with their owner and kept mark. */
function roots(): Root[] {
  const found: Root[] = [];
  for (const name of readdirSync(tmpdir())) {
    if (!name.startsWith(prefix)) continue;
    const path = join(tmpdir(), name);
    try {
      const recorded = Number(readFileSync(join(path, owner), "utf8"));
      found.push({
        path,
        pid: Number.isInteger(recorded) && recorded > 0 ? recorded : null,
        kept: readdirSync(path).includes(keptMark),
        mtimeMs: statSync(path).mtimeMs,
      });
    } catch {
      // A root without a readable owner is being created or removed: left alone.
    }
  }
  return found;
}

/** Remove kept roots beyond the newest `keptRoots`, and unkept roots whose
 * creating process is gone. A live process's unkept root is never touched. */
function prune(): void {
  const all = roots();
  for (const root of all)
    if (!root.kept && root.pid !== null && root.pid !== process.pid && !alive(root.pid))
      rmSync(root.path, { recursive: true, force: true });
  const keptOnes = all.filter((root) => root.kept).sort((a, b) => b.mtimeMs - a.mtimeMs);
  for (const root of keptOnes.slice(keptRoots)) rmSync(root.path, { recursive: true, force: true });
}

/** This invocation's root, created on first use. */
export function runRoot(): string {
  const inherited = process.env[variable];
  if (inherited) return inherited;
  prune();
  const created = mkdtempSync(join(tmpdir(), prefix));
  writeFileSync(join(created, owner), String(process.pid));
  process.env[variable] = created;
  const finish = (): void => {
    if (!kept) rmSync(created, { recursive: true, force: true });
    else {
      writeFileSync(join(created, keptMark), "");
      prune();
    }
  };
  process.on("exit", finish);
  for (const signal of ["SIGINT", "SIGTERM", "SIGHUP"] as const)
    process.once(signal, () => {
      finish();
      process.kill(process.pid, signal);
    });
  return created;
}

/** A fresh directory under this invocation's root, named from `prefix`. */
export function runDirectory(name: string): string {
  const root = runRoot();
  requireDiskSpace();
  return mkdtempSync(join(root, name));
}

/** Keep this invocation's directories after it exits: for a command that
 * prints one for inspection. A process that inherited its root leaves the
 * decision to the process that created it. */
export function keepRunDirectories(): void {
  kept = true;
}

/** Stop a driver before another run when the artifact volume has less than
 * 10 GiB available. This is a resource failure, not a source verdict. */
export function requireDiskSpace(): void {
  const volume = process.env[variable] ?? tmpdir();
  const space = statfsSync(volume);
  const available = space.bavail * space.bsize;
  if (available < 10 * 1024 ** 3) {
    process.stderr.write(`TScert stopped: ${(available / 1024 ** 3).toFixed(2)} GiB free at ${volume}; at least 10 GiB required.\n`);
    process.exit(1);
  }
}

/** Own a result's artifacts until its caller finishes reading them. Callers
 * bind the returned value with `using`; disposal also runs on exceptions.
 * Explicitly kept command-line runs retain their artifacts for inspection. */
export function ownedRun<T extends { artifacts: string }>(result: T, retain: boolean = false): T & Disposable {
  const owned = Object.assign(result, { [Symbol.dispose](): void {
    if (!kept) rmSync(result.artifacts, { recursive: true, force: true });
  } });
  Object.defineProperty(owned, Symbol.dispose, { enumerable: false });
  if (!retain) owned[Symbol.dispose]();
  return owned;
}
