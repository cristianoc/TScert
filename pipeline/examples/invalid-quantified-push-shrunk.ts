// A push extending a quantified fact, then a `pop` of the array bounding its
// elements: the pushed `widths.length - 1` may now be the length, and the
// loop's head refuses its entry (run under Node: `sumAfterShrink([5], [])`
// pushes `0`, pops `widths`, then reads `widths[0]`, `undefined` at
// `number`).

/**
 * @requires 1 <= widths.length
 * @requires forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length
 */
export function sumAfterShrink(widths: number[], ends: number[]): number {
  ends.push(widths.length - 1);
  widths.pop();
  let total = 0;
  /** @invariant forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length */
  for (let i = 0; i < ends.length; i++) total += widths[ends[i]!]!;
  return total;
}
