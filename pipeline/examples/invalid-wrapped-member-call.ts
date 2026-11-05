// A call of an element read through `!`, with the array as its receiver:
// the read is the element's type or `undefined` (an index past the end),
// and `!` does not rule `undefined` out, so the callee's cast is unmet.
export function wrapped(fs: readonly (() => number)[], i: number): number {
  return fs[i]!();
}
