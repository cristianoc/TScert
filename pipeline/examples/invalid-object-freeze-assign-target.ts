// `Object.assign` onto a frozen literal sets its field, which throws (run
// under Node: TypeError, "Cannot assign to read only property").
export function f(a: number): { readonly a: number } {
  return Object.assign(Object.freeze({ a }), { a: a + 1 });
}
