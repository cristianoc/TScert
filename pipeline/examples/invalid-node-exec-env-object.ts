import { execFileSync } from "node:child_process";

// Options whose type does not name `env` may carry one: the host converts
// an `env` value to a string, which runs that value's `toString`, before
// it reads the `stdio` array, and the `toString` may set it to ignore
// standard output. Called with
// `{ encoding: "utf8", stdio, env: { X: { toString() { stdio[1] = "ignore"; return "x"; } } } }`,
// `run` returns `null`.
export type Options = {
  encoding: "utf8";
  input?: string;
  maxBuffer?: number;
  stdio?: readonly ["pipe", "pipe", "ignore"];
};

export function run(args: string[], options: Options): string {
  return execFileSync("node", args, options);
}
