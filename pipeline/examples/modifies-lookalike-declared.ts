// A file declaring its own `Modifies`: a reference to it is an ordinary
// type, read as its alias, and states nothing.
type Modifies<P, T> = T;

export function size(xs: number[]): Modifies<{ values: "any" }, number> {
  return xs.length;
}
