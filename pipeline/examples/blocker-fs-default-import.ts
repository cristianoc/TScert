// `fs` imported by default from `node:fs`: the module's object, read through
// its members, each the named export it holds; `existsSync` is read through
// its reviewed entry.
// Census functions:
// unchecked.mts#check, unchecked.mts#findIn.
import fs from "node:fs";
export function exists(path: string): boolean {
  return fs.existsSync(path);
}
