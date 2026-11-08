// Pretext getFontData's group and getHanKerningTrims' addWidthTrim capture the bounded storage.
export function first(xs: number[]): number {
  /** @requires safeInteger(i) && 0 <= i && i < xs.length */
  const at = (i: number): number => xs[i]!;
  return xs.length > 0 ? at(0) : 0;
}
