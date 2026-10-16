import { execFileSync } from "node:child_process";

// With standard output not piped to the parent, `execFileSync` returns
// `null`, though its declaration says `string` at a text encoding:
// `run(["-e", ""])` is `null`.
export function run(args: string[]): string {
  return execFileSync("node", args, {
    encoding: "utf8",
    stdio: ["pipe", "ignore", "ignore"],
  });
}
