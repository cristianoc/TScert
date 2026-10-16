// A value of one type parameter is not of its meet with another: the meet
// row is below the binder, not above it.
export function widen<T, U>(x: T): T & U {
  return x;
}
