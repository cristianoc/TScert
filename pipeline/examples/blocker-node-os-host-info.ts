// `availableParallelism()` and `userInfo()` from `node:os` as the census
// sites use them, under the declarations the front end is checked with: the
// number of a check's parts, and the home directory a launcher's profile
// names.
// Census functions: unchecked.mts#check, unchecked.mts#findIn,
// unchecked.mts#decodeResult, compiler-channel.mts#identify,
// compiler-channel.mts#launcher.
import { availableParallelism, userInfo } from "node:os";

export const parts: number = Math.max(1, Math.min(8, availableParallelism() - 1));

export function profile(directory: string): string {
  return `${directory}:${userInfo().homedir}`;
}
