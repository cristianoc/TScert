// The inclusive disjunct admits index === widths.length.
/** @requires safeInteger(end) && safeInteger(index) && 0 <= index
 * @requires end <= 0 || index <= widths.length
 */
export function terminal(widths: number[], end: number, index: number): number {
  if (end <= 0) return 0;
  return widths[index]! + 1;
}
