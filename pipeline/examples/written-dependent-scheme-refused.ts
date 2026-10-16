// A generic function type whose binder's bound names another of its
// binders: the scheme's dependent bound has no representation.
export function f(g: <T, U extends T>(u: U) => T): number {
  return 1;
}
