// Temporary directories of one invocation. Every directory a run, a check or
// a test writes lies under one root per process tree: the first process to
// ask creates it, the processes it forks inherit it through the environment,
// and the creating process removes it when it exits. A command that prints a
// run's directory for inspection keeps the root instead.

import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const variable = "TSCERT_RUN_ROOT";
let kept = false;

/** This invocation's root, created on first use. */
export function runRoot(): string {
  const inherited = process.env[variable];
  if (inherited) return inherited;
  const created = mkdtempSync(join(tmpdir(), "tscert-runs-"));
  process.env[variable] = created;
  const remove = (): void => {
    if (!kept) rmSync(created, { recursive: true, force: true });
  };
  process.on("exit", remove);
  for (const signal of ["SIGINT", "SIGTERM", "SIGHUP"] as const)
    process.once(signal, () => {
      remove();
      process.kill(process.pid, signal);
    });
  return created;
}

/** A fresh directory under this invocation's root, named from `prefix`. */
export function runDirectory(prefix: string): string {
  return mkdtempSync(join(runRoot(), prefix));
}

/** Keep this invocation's directories after it exits: for a command that
 * prints one for inspection. A process that inherited its root leaves the
 * decision to the process that created it. */
export function keepRunDirectories(): void {
  kept = true;
}
