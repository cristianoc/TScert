// Pretext han-kerning's local helper: a call must establish its bounds.
export function broken(xs: number[]): number {
  /** @requires safeInteger(i) && 0 <= i && i < ys.length */
  const at = (ys: number[], i: number): number => ys[i]!;
  return at(xs, xs.length);
}
