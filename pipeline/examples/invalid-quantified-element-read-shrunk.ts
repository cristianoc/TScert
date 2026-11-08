// A quantified fact bounding elements by an array's length, across a `pop`
// that shrinks that array: the element the fact bounded may now be the
// length (run under Node: `widthAfterPop([5], [0], 0)` pops `widths`, then
// reads `widths[0]`, `undefined` at `number`).

/** @requires safeInteger(k) && 0 <= k && k < ends.length
 * @requires forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length */
export function widthAfterPop(
  widths: number[],
  ends: number[],
  k: number,
): number {
  widths.pop();
  return widths[ends[k]!]!;
}
