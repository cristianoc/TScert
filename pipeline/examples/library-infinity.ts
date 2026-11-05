// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// line-break.ts#normalizeMaxWidth.
// The global `Infinity`, a non-writable, non-configurable data property of
// the global object: read as a value, a number.
export function normalize(maxWidth: number): number {
  return maxWidth <= Infinity ? maxWidth : Infinity;
}
