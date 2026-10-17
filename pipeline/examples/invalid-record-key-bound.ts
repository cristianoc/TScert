// A library mapped type's key argument keeps the bound of the application
// it replaces.
type Key<T extends string> = "a";
export function f(x: Record<Key<number>, number>): number {
  return x.a;
}
