// An index signature's key keeps the bound of the application it is.
type Key<T extends string> = string;
export function f(x: { [k: Key<number>]: number }): number {
  return 1;
}
