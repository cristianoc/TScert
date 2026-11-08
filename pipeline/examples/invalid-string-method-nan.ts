// Pretext range tests cannot reject NaN: both comparisons are false.
/** @requires safeInteger(c) && 0 <= c && c <= 65535 */
function unit(c: number): number { return c; }
export function outOfBounds(s: string): number {
  const c = s.charCodeAt(s.length);
  if (c < 0 || c > 65535) return 0;
  return unit(c);
}
