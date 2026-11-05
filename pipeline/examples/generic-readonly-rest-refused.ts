// A generic module function's rest typed by a readonly array: the array a
// call collects is fresh, so the readonly view gives up only writes, but the
// scheme of a generic module function states its rest as a mutable array's
// element, and the readonly contract is refused at the function.
export function firstOr<T>(fallback: T, ...xs: readonly T[]): T {
  const [x] = xs;
  return x === undefined ? fallback : x;
}
export function use(): number {
  return firstOr(0, 1, 2);
}
