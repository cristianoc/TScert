// Bounds pattern P9: a product of two variables in an index.
// Fact: rows.length = states * width and 0 <= state < states, so
// state * width + c < rows.length for 0 <= c < width.
// Pretext: graphemes.ts parseGraphemeRules, findGraphemeEnds; line-breaks.ts
// markRuleBoundaries (7 sites).
// Gap: the clause language admits a product of a literal and a path only;
// the precondition is refused at the source.
/** @requires safeInteger(width) && 0 < width && width <= 64 && safeInteger(states) && 0 < states && states <= 1024
 * @requires rows.length === states * width */
export function badProduct(rows: Uint16Array, width: number, states: number, state: number): number {
  if (!(state >= 0 && state < states)) return 0;
  return rows[state * width]!;
}
