// `sort` mutates its receiver, so it takes a mutable array; a readonly one
// is refused.
function ascending(xs: readonly number[]): readonly number[] {
  return xs.sort((a: number, b: number): number => a - b);
}
