// `spawnSync` at a text encoding with both streams piped: its output is a
// string where the child ran, absent where it could not be spawned.
import { spawnSync } from "node:child_process";

export function output(command: string, args: readonly string[]): string {
  const ran = spawnSync(command, args, { encoding: "utf8", timeout: 30_000 });
  if (ran.error !== undefined || ran.status !== 0) return "";
  return ran.stdout ?? "";
}
