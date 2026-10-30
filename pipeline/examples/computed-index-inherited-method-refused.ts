// An indexed access at an optional method an interface inherits: its
// function takes the interface declaring it, Base, as its receiver, which
// the reference Derived does not name.
interface Base {
  m?(): number;
}
interface Derived extends Base {
  extra: string;
}
export function f(d: Derived): Derived["m"] {
  return d.m;
}
