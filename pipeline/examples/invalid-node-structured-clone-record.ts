// A record typed by its fields may hold a getter, which `structuredClone`
// runs, and a prototype the copy loses (run under Node: the getter runs and
// the copy holds a data property): it is no JSON value, so the call is
// refused.
export function copy(o: { readonly a: number }): unknown {
  return structuredClone(o);
}
