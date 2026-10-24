// A footprint written through an alias: a statement's footprint is a type
// literal written in place.
type Keeps = { value: "keep"; store: "keep" };

export function f(n: number): Within<Keeps, number> {
  return n;
}
