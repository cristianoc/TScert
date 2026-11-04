// A frozen literal passed where a parameter's field is writable: the
// callee's write throws (run under Node: TypeError, "Cannot assign to read
// only property").
function bump(o: { a: number }): void {
  o.a = o.a + 1;
}

export function f(a: number): void {
  bump(Object.freeze({ a }));
}
