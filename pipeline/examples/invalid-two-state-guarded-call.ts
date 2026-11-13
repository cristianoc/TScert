// The unsafe neighbour of `two-state-guarded-call`: the caller reads the
// last element whether or not `grow` held, but `maybeAppend` grows `xs`
// only where `grow` is not false, so an empty `xs` is read at -1.

/**
 * @requires 0 <= xs.length && xs.length <= 1000
 * @ensures grow === false || xs.length === old(xs.length) + 1
 */
function maybeAppend(xs: number[], grow: boolean): Modifies<{ values: "any"; stores: "grow" }, void> {
  if (!grow) return;
  xs.push(0);
}

/** @requires 0 <= xs.length && xs.length <= 1000 */
export function lastAppended(xs: number[], grow: boolean): number {
  maybeAppend(xs, grow);
  return xs[xs.length - 1]!;
}
