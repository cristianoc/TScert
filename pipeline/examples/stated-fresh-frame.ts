// A frame and a fresh result, `Modifies<P, Fresh<T>>`: `copy` changes no
// location and returns the array `slice` allocates.
export function copy(xs: readonly number[]): Modifies<{}, Fresh<number[]>> {
  return xs.slice();
}
