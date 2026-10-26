// A mapped type whose value is `X[P]` at a named type X: the reader holds a
// reference there, not X's members, and refuses it.
type Source = { readonly a: number; b?: string };

export function read(p: Readonly<Source>): number {
  return p.a;
}
