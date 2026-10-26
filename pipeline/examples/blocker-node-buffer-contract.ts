// `statSync(path).size` through `statSync`'s reviewed entry: its declaration,
// which reaches `Buffer` through `PathLike`, is not read.
// Census functions:
// family-activation.mts#declarationInventory, files.mts#attemptAnswer,
// files.mts#findPackage, files.mts#installed, files.mts#kindOf,
// files.mts#manifestField, files.mts#privateLauncher, files.mts#realOf,
// files.mts#realPath.
import { statSync } from "node:fs";
export function use(path: string): number {
  return statSync(path).size;
}
