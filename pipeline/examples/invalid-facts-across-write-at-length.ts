// A write at `j + 1` where `j` is the last index lands at the length and
// grows the array, so `other.length === flags.length` does not survive it.
// Under Node, `grown([1], [2])` reads `other[1]`, `undefined` at `number`,
// and answers `undefined`.

/** @requires other.length === flags.length && 1 <= flags.length && flags.length <= 4294967294 */
export function grown(flags: number[], other: number[]): number {
  const j = flags.length - 1;
  flags[j + 1] = 0;
  return other[flags.length - 1]!;
}
