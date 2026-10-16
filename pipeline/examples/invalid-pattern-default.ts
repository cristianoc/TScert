// A default replaces only an undefined read: the binding holds the default's
// type too, which the return contract does not admit.
export function otherType(x: { f?: number }): number {
  const { f = "a" } = x;
  return f;
}
