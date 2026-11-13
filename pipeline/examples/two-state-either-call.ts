// Rule Call for a two-state postcondition under a disjunction: `appendSome`
// grows `xs` by one or by two, so after the call `xs` is at least one
// longer than just before it.

/**
 * @requires 0 <= xs.length && xs.length <= 1000
 * @ensures xs.length === old(xs.length) + 1 || xs.length === old(xs.length) + 2
 */
function appendSome(xs: number[], two: boolean): Modifies<{ values: "any"; stores: "grow" }, void> {
  xs.push(0);
  if (!two) return;
  xs.push(1);
}

/** @requires 0 <= xs.length && xs.length <= 1000 */
export function lastOfSome(xs: number[], two: boolean): number {
  appendSome(xs, two);
  return xs[xs.length - 1]!;
}
