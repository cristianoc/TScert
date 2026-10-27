// A function imported from node:url, read through Node's declarations of the
// module, which reach URLSearchParams and BuiltinIteratorReturn.
// Census functions:
// family-activation.mts#activeGuards, family-activation.mts#loadedGuards,
// family-activation.mts#selectionGuard and 9 others of family-activation.mts,
// files.mts#nodeResolve, files.mts#loadModule, files.mts#observeResolution,
// files.mts#resolveObserved, unchecked.mts#check, unchecked.mts#findIn,
// unchecked.mts#isResult.
import { fileURLToPath } from "node:url";

export function pathOf(url: string): string {
  return fileURLToPath(url);
}
