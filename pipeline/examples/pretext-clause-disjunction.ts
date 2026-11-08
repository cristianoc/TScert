// Pretext getTerminalLetterSpacing: a linear disjunction permits an early
// return; its other arm bounds the element read.
/** @requires safeInteger(end) && safeInteger(index) && 0 <= index
 * @requires end <= 0 || index < widths.length
 */
export function terminal(widths: number[], end: number, index: number): number {
  if (end <= 0) return 0;
  return widths[index]!;
}

export function callTerminal(widths: number[]): number {
  if (widths.length > 0) return terminal(widths, 1, 0);
  return terminal(widths, 0, 0);
}

/** @requires safeInteger(end) && safeInteger(index) && 0 <= index
 * @requires !(end > 0) || index < widths.length
 */
export function implication(
  widths: number[],
  end: number,
  index: number,
): number {
  if (end <= 0) return 0;
  return widths[index]!;
}

/** @requires safeInteger(end) && safeInteger(i) && safeInteger(j) && 0 <= i && 0 <= j
 * @requires end <= 0 || (i < widths.length && j < widths.length)
 */
export function conjunction(
  widths: number[],
  end: number,
  i: number,
  j: number,
): number {
  if (end <= 0) return 0;
  return widths[i]! + widths[j]!;
}
