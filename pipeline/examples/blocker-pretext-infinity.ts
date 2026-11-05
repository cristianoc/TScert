// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// line-break.ts#normalizeMaxWidth.
// Refusal: gate: the global Infinity is declared in
// typescript/lib/lib.es5.d.ts (library), an origin no reviewed entry
// admits.
// The global `Infinity`, which has no reviewed entry.
export function normalize(maxWidth: number): number {
  return maxWidth <= Infinity ? maxWidth : Infinity;
}
