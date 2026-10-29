// A parameter pattern whose later default reads an earlier binding the
// function assigns: JavaScript binds `a` before `b`'s default reads it (run
// under Node: `f({})` returns 1). Refused at the gate: an assigned pattern
// binding is not lowered.
export function f({ a = 1, b = a }: { a?: number; b?: number }): number {
  a = 2;
  return b;
}
