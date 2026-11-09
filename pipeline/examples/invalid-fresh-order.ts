// A frame inside `Fresh`: the one order is `Modifies<P, Fresh<T>>`.
export function copy(xs: readonly number[]): Fresh<Modifies<{}, number[]>> {
  return xs.slice();
}
