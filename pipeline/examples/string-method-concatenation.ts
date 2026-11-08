// Pretext: transformText builds its result from string slices.
/** @requires safeInteger(n) && s.length === n */
function sized(s: string, n: number): string { return s; }
export function concatenated(s: string, t: string): string {
  const joined = s + t;
  return sized(joined, s.length + t.length);
}
