// Distinct field names can hold the same array. Under Node the function
// returns undefined for widths=[7], pair={left:[0],right:thatSameArray}, k=0.
/** @requires safeInteger(k) && 0 <= k && k < pair.right.length
 * @requires forall i in pair.right: safeInteger(pair.right[i]) && 0 <= pair.right[i] && pair.right[i] < widths.length */
export function afterFieldAlias(widths: number[], pair: {left: number[]; right: number[]}, k: number): number {
  if (k < pair.left.length) pair.left[k] = widths.length;
  return widths[pair.right[k]!]!;
}
