/** @requires safeInteger(n) && 0 < n && n <= 4294967295 */
export function past(n: number): string {
  const xs = new Array<string>(n).fill("ok");
  return xs[n]!.toUpperCase();
}
