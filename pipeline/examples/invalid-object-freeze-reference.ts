// `Object.freeze` of a local holding a literal: the local keeps its
// writable type, and its write throws (run under Node: TypeError, "Cannot
// assign to read only property"). Only a literal written as the argument,
// which no other reference holds, is admitted.
export function f(a: number): number {
  const o = { a };
  Object.freeze(o);
  o.a = a + 1;
  return o.a;
}
