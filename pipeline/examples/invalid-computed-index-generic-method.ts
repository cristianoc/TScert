// An indexed access at a required method, here a generic one: a method's
// member is relative to the object it is read from, and no function type
// states it apart from that object.
type A = { g<T>(x: T): T; size: number };
export function f(a: A): A["g"] {
  return a.g;
}
