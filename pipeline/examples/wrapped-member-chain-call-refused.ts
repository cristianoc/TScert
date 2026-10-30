// A call of an element read in an optional chain through `!`: on the
// chain's present value the read is the element's type or `undefined`,
// which `!` does not rule out, as outside a chain.
export function wrapped(
  fs: readonly (() => number)[] | undefined,
  i: number,
): number | undefined {
  return fs?.[i]!();
}
