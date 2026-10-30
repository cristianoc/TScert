// A `switch` whose `case` labels are enum members narrows as the same test
// written with `===` does: each test reads the discriminant again, since
// reading an enum member writes nothing. A clause sees the arm its label
// selects, `default` the rest, for a name and a field of a name, a
// `const enum`'s members too, and a `default` written between cases
// (`switch-enum-value-import` for an imported enum).
const enum C {
  Red = "red",
  Blue = "blue",
}
type R = { readonly c: C.Red; readonly r: number };
type U = { readonly c: C.Blue; readonly u: number };

export function middleDefault(v: R | U): number {
  switch (v.c) {
    case C.Red:
      return v.r;
    default:
      return v.u;
    case C.Blue:
      return v.u;
  }
}

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
      return n.b;
  }
}

export function both(k: K): 1 | 2 {
  switch (k) {
    case K.One: {
      const one: K.One = k;
      return one;
    }
    case K.Two: {
      const two: K.Two = k;
      return two;
    }
  }
}
