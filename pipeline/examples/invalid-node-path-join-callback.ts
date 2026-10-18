// `join` calls `posix.normalize`, a property other code may replace by a
// function that shrinks the array `map` visits (run under Node): the call
// is unrestricted, and the mapped array may be sparse.
import { join } from "node:path";

export function parents(files: string[]): string[] {
  return files.map((f) => join(f, ".."));
}
