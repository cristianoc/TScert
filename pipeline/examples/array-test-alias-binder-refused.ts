// `Array.isArray` of a value of an alias whose definition names a type
// parameter keeps the parameter's arm, of which nothing is known: its
// `length` is not read, though an array the test found has one.
type A<T> = { a: number } | T;
export function size<T>(x: A<T>): number {
  if (Array.isArray(x)) return x.length;
  return 0;
}
