// With `stdio` naming no pipe, the child's output is not captured and
// `stdout` is `null` (run under Node), though the declaration says `string`:
// the reviewed entry states the options without `stdio`, so the call is
// refused.
import { spawnSync } from "node:child_process";

export function output(command: string): string {
  return spawnSync(command, [], { encoding: "utf8", stdio: "ignore" }).stdout;
}
