// `ReadonlyArray<T>` is `readonly T[]`: a view grants no write, so it is not
// the mutable `Array<T>` a caller could push through.
function widen(xs: ReadonlyArray<number>): Array<number> {
  return xs;
}
