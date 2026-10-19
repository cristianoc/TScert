// An entry's `isDirectory` dispatches through a prototype other code may
// change (run under Node: a replaced `Dirent.prototype.isDirectory` answers
// 7): its result is `unknown`, refused as a Boolean.
import { readdirSync } from "node:fs";

export function flags(dir: string): boolean[] {
  const found: boolean[] = [];
  for (const entry of readdirSync(dir, { withFileTypes: true }))
    found.push(entry.isDirectory());
  return found;
}
