// A quantified precondition bounding elements by `widths.length` inclusively
// bounds no read at an element: `ends[i] <= widths.length` admits an element
// equal to the length, at which `widths` holds nothing (run under Node:
// `widthAt([5], [1], 0)` reads `widths[1]`, `undefined` at `number`).

/** @requires safeInteger(k) && 0 <= k && k < ends.length
 * @requires forall i in ends: safeInteger(ends[i]) && 0 <= ends[i] && ends[i] <= widths.length */
export function widthAt(widths: number[], ends: number[], k: number): number {
  return widths[ends[k]!]!;
}
