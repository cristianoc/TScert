// TypeScript gives a frozen literal's `Readonly<T>` to a binding of a type
// with a writable field; the write then throws (run under Node: TypeError,
// "Cannot assign to read only property"). The result's readonly view is
// not a writable field.
export function f(a: number): number {
  const w: { a: number } = Object.freeze({ a });
  w.a = a + 1;
  return w.a;
}
