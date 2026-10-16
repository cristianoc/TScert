import { execFileSync } from "node:child_process";
import { writeFileSync } from "fs";

// Node's `execFileSync` at a text encoding, standard output piped, returns
// the child's output as a string; `writeFileSync` of a string to a path
// returns nothing. Both are read through the reviewed overlay of library
// modules, `node:fs` and `fs` naming one module.
export function run(args: string[], input?: string): string {
  return execFileSync("node", args, {
    input,
    encoding: "utf8",
    maxBuffer: 1024 * 1024,
    stdio: ["pipe", "pipe", "ignore"],
  });
}

export function plain(args: readonly string[]): string {
  return execFileSync("node", args, { encoding: "utf8" });
}

export function save(path: string, text: string): void {
  writeFileSync(path, text);
}
