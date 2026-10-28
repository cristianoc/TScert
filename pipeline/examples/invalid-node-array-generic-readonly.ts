// Under Node's types, which merge `RelativeIndexable<T>` into both
// interfaces, `ReadonlyArray<T>` is still `readonly T[]`: a view grants no
// write, so it is not the mutable `Array<T>` a caller could push through.
export function widen(xs: ReadonlyArray<number>): Array<number> {
  return xs;
}
