// Negative control: an ordinary Array read `xs[k] !== undefined` does NOT imply
// `0 <= k < xs.length`, because a plain JS Array can hold an own property at a
// non-index numeric key (e.g. `-1`), where a parallel array `ys[k]` reads
// `undefined` (observed `NaN` under Node).

export function badArrayReadDefined(
  xs: number[],
  ys: number[],
  k: number,
): number {
  if (ys.length !== xs.length) return 0;
  const v = xs[k];
  if (v === undefined) throw new RangeError("missing");
  return v + ys[k]!;
}
