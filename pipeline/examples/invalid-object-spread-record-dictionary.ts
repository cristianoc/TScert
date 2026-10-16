// A record type is open: a spread of one may copy keys it does not state, at
// any type, so the result meets no index.
export function view(a: { x: number }): { readonly [k: string]: number } {
  return { ...a };
}
