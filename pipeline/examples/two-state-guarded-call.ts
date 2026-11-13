// Rule Call for a two-state postcondition under a guard: `maybeAppend`
// grows `xs` by one where `grow` is not false, so after the call, on the
// branch where `grow` holds, `xs` is one longer than just before it.

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
  if (grow) return xs[xs.length - 1]!;
  return 0;
}
