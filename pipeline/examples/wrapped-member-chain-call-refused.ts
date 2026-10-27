// A call of a member read in an optional chain through `!`: as outside a
// chain, refused rather than called without its receiver.
export function wrapped(
  fs: readonly (() => number)[] | undefined,
  i: number,
): number | undefined {
  return fs?.[i]!();
}
