// A `switch` whose `case` labels are enum members narrows as the same test
// written with `===` does: here the first case reads `a`, which only `A`
// holds.
enum K {
  One = 1,
  Two = 2,
}
type A = { readonly kind: K.One; readonly a: string };
type B = { readonly kind: K.Two; readonly b: string };

export function read(n: A | B): string {
  switch (n.kind) {
    case K.One:
      return n.a;
    default:
      return "";
  }
}
