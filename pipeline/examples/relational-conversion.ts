// An index read past an array's end is `undefined`, which TypeScript types as
// the element: `<` converts it by `ToNumeric` to NaN, and NaN compares false.
export function negativeFirst(values: number[]): boolean {
  const first = values[0];
  return first < 0;
}

// A bigint compares exactly with a number.
export function belowLimit(n: number, limit: bigint): boolean {
  return n < limit;
}
