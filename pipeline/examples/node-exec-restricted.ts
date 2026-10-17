import { execFileSync } from "node:child_process";

// `execFileSync` at options naming no `env`, `shell` absent and standard
// error ignored writes nothing it did not allocate, before it returns or
// throws: its restricted form states the empty footprint on a throw too. A
// handler catching its throw, here a failed command, stays within the
// caller's footprint, and a callback calling the catching function keeps
// `map`'s result dense.
const run = (args: string[], input?: string): string =>
  execFileSync("node", args, {
    input,
    encoding: "utf8",
    maxBuffer: 1024 * 1024,
    stdio: ["pipe", "pipe", "ignore"],
  });

export function outputOrNone(args: string[]): string | undefined {
  try {
    return run(args);
  } catch {
    return undefined;
  }
}

export function outputs(scripts: string[]): string[] {
  return scripts.map((s: string): string => outputOrNone(["-e", s]) ?? "");
}
