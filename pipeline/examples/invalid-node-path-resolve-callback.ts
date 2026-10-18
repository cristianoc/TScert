// `resolve` reads `process.cwd()` for a relative path, a property other
// code may replace by a function that shrinks the array `map` visits (run
// under Node): the call is unrestricted, and the mapped array may be sparse.
import { resolve } from "node:path";

export function absolute(files: string[]): string[] {
  return files.map((f) => resolve(f));
}
