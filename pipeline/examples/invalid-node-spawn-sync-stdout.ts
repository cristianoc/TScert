// A command that cannot be spawned leaves `stdout` absent (run under Node:
// `undefined`), though the declaration says `string`: refused as a string.
import { spawnSync } from "node:child_process";

export function output(command: string): string {
  return spawnSync(command, [], { encoding: "utf8" }).stdout;
}
