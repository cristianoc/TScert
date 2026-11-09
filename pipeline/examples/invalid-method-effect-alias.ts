// A footprint written through an alias: a statement's footprint is a type
// literal written in place.
type Keeps = {};

export function f(n: number): Modifies<Keeps, number> {
  return n;
}
