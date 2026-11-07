// A read at an index the comparison bounds by the store's length: the read's
// claim stays `undefined | number`; a bound read's element contract is not
// stated.
export function first(xs: number[]): number {
  let j = 0;
  if (j < xs.length) return xs[j];
  return 0;
}
