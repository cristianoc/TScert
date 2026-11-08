// pretext's analyzeText: a `let` assigned the result of a call stating a
// postcondition, in each arm of a conditional, takes the postcondition's
// facts as a declaration does, so the reads below the view's length verify.
/** @ensures result.length === s.length + 1 */
function lineBreaks(s: string): Uint8Array {
  return new Uint8Array(s.length + 1);
}
/** @ensures result.length === s.length + 1 */
function paragraphBreaks(s: string, items: number): Uint8Array {
  return items < 0
    ? new Uint8Array(s.length + 1)
    : new Uint8Array(s.length + 1);
}
export function sumBreaks(s: string, items: number | null): number {
  let breaks: Uint8Array;
  breaks = items === null ? lineBreaks(s) : paragraphBreaks(s, items);
  let total = 0;
  for (let i = 0; i <= s.length; i++) total += breaks[i]!;
  return total;
}
