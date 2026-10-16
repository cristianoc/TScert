// A function type met with a record of readonly fields is a callable with
// a readonly field, which no clause states.
export function call(h: (() => void) & { readonly a: number }): number {
  h();
  return h.a;
}
