// An enum-member label narrows to the arm it selects alone: the clause of
// `K.Two` reads `a`, which only the arm of `K.One` holds.
enum K {
  One = 1,
  Two = 2,
}
type A = { readonly kind: K.One; readonly a: string };
type B = { readonly kind: K.Two; readonly b: string };

export function read(n: A | B): string {
  switch (n.kind) {
    case K.Two:
      return n.a;
    default:
      return "";
  }
}
