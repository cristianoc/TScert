// `Array<T>` is `T[]`, invariant in `T`: a string pushed through the wider
// type would reach readers of the numbers.
function widen(xs: Array<number>): Array<number | string> {
  return xs;
}
