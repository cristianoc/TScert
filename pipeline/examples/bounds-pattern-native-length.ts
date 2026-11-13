// Bounds pattern P14, the supported neighbour of
// `bounds-pattern-native-length-refused`: `slice`, whose length contract is exact.
// Pretext: analysis.ts analyzeText.
/** @requires safeInteger(k) && 0 <= k && k <= text.length */
export function goodSlice(text: string, k: number): number {
  const head = text.slice(0, k);
  const breaks = new Uint8Array(text.length + 1);
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && head.length <= text.length && breaks.length === text.length + 1 */
  for (let i = 0; i < head.length; i++) s += breaks[i]!;
  return s;
}
