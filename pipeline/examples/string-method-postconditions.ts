// Pretext: getKanaKerning, measureKanaKerning and the text scanners.
/** @requires safeInteger(c) && 0 <= c && c <= 65535 */
function unit(c: number): number { return c; }
/** @requires safeInteger(n) && s.length === n */
function sized(s: string, n: number): string { return s; }
/** @requires safeInteger(r) && -1 <= r && r <= s.length */
function found(s: string, r: number): number { return r; }
/** @requires safeInteger(i) && 0 <= i && i < s.length */
export function codeUnit(s: string, i: number): number {
  const c = s.charCodeAt(i);
  return unit(c);
}
/** @requires safeInteger(a) && safeInteger(b) && 0 <= a && a <= b && b <= s.length */
export function sliceLength(s: string, a: number, b: number): string {
  const part = s.slice(a, b);
  return sized(part, b - a);
}
export function search(s: string, needle: string): number {
  const r = s.indexOf(needle);
  return found(s, r);
}
export function searchLast(s: string, needle: string): number {
  const r = s.lastIndexOf(needle);
  return found(s, r);
}


/** @requires safeInteger(r) && -1 <= r && r < s.length */
function strictlyFound(s: string, r: number): number { return r; }
/** @requires 0 < needle.length */
export function nonemptySearch(s: string, needle: string): number {
  const r = s.indexOf(needle);
  return strictlyFound(s, r);
}
/** @requires 0 < needle.length */
export function nonemptyLast(s: string, needle: string): number {
  const r = s.lastIndexOf(needle);
  return strictlyFound(s, r);
}
