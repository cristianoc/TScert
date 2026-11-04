// A frozen literal held at a type with an optional field it lacks: adding
// the key throws, the object being non-extensible (run under Node:
// TypeError, "Cannot add property b, object is not extensible").
export function f(a: number): number {
  const w: { a: number; b?: number } = Object.freeze({ a });
  w.b = a;
  return w.b;
}
