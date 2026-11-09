// `Fresh` on a result of no array type: a fresh result is an array the call
// allocated.
export function count(xs: readonly number[]): Fresh<number> {
  return xs.length;
}
