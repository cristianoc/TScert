// A mapped type's keys keep the bound of the application they replace.
type Key<T extends string> = "a" | T;
export function f(x: { [K in Key<number>]: number }): number {
  return x.a;
}
