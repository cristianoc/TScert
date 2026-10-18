// A property named as a later constant is no mention of it: no binding is
// early, and the file lists no `%ThrowUninitialized%`.
export function sum(o: { x: number }): number {
  const y = o.x;
  const x = 1;
  return x + y;
}
