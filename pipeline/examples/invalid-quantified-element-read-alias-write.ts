// A quantified fact across a write through an alias of its array: the write
// stores the length itself, which the fact excluded, so the read after it is
// past the end (run under Node: `widthAfterWrite([5], [0], 0)` stores `1`
// through `alias`, then reads `widths[1]`, `undefined` at `number`).

/** @requires safeInteger(k) && 0 <= k && k < ends.length
 * @requires forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] < widths.length */
export function widthAfterWrite(
  widths: number[],
  ends: number[],
  k: number,
): number {
  const alias = ends;
  if (k < alias.length) alias[k] = widths.length;
  return widths[ends[k]!]!;
}
