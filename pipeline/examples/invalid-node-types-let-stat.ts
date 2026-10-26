// `statSync` under the variant declarations of pipeline/node-types-let-project,
// whose call signature is the reviewed one: refused at the import.
import { statSync } from "node:fs";

export function size(path: string): number {
  return statSync(path).size;
}
