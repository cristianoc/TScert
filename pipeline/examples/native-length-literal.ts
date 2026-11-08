// Pretext: han-kerning.ts#getFontData's glyph literals.
/** @requires safeInteger(k) && 0 <= k && k < 2 */
export function literal(a: string, b: string, k: number): string {
  const xs: string[] = [a, b];
  return xs[k]!.toUpperCase();
}
/** @requires safeInteger(k) && 0 <= k && k < 2 */
export function literalMap(k: number): string {
  const xs = ["a", "b"].map((x) => x.toUpperCase());
  return xs[k]!.toUpperCase();
}
export function order(): string {
  let n = 0;
  const xs: number[] = [n++, n++];
  return `${xs[0]},${xs[1]},${n}`;
}

/** @requires safeInteger(k) && 0 <= k && k < 2 */
export function twoLiterals(a: string, b: string, k: number): string {
  const xs: string[] = [a, b];
  const ys: string[] = [b];
  return xs[k]!.toUpperCase() + ys[0]!.toUpperCase();
}
