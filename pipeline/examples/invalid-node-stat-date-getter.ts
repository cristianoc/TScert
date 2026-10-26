// A `Stats`'s `mtime` is a getter of `Stats.prototype`, which other code may
// replace (run under Node: a replaced getter runs at the read and answers a
// number). The reviewed entry states the own numbers alone: refused.
import { statSync } from "node:fs";

export function modified(path: string): Date {
  return statSync(path).mtime;
}
