// Node's fs read through a default import needs the module's namespace as
// the import's value.
// Census functions:
// unchecked.mts#check, unchecked.mts#findIn.
import fs from "node:fs";
export function exists(path: string): boolean {
  return fs.existsSync(path);
}
