// A `Stats`'s `isFile` calls `this._checkModeProperty`, a writable property
// of `Stats.prototype` other code may replace (run under Node: a replaced
// one answers 7): its result is `unknown`, refused as a Boolean.
import { statSync } from "node:fs";

export function isFile(path: string): boolean {
  return statSync(path).isFile();
}
