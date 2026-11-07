// A write at an index the comparison bounds by the store's length: the
// comparison's true edge carries the linear fact `j - length <= -1`, the
// length read states the store's length, and the write reads the bound from
// them. The index is a literal, a copy of one, and a two-sided test.
export function setFirst(xs: number[]): void {
  let j = 0;
  if (j < xs.length) xs[j] = 0;
}

export function setCopied(xs: number[]): void {
  let j = 0;
  const m = j;
  if (m < xs.length) xs[m] = 0;
}

export function setTwoSided(xs: number[]): void {
  let j = 0;
  if (j >= 0 && j < xs.length) xs[j] = 0;
}
