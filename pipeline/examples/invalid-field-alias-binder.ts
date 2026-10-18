// A field declared at an alias whose definition names a type parameter may
// hold a number where the parameter is `number`: a test finding a number
// there excludes no arm, and the read of `n` is refused.
type Alias<T> = string | T;
type Box<T> = { value: Alias<T> } | { value: number; n: number };
export function wrong<T>(b: Box<T>): number {
  if (typeof b.value === "number") return b.n;
  return 0;
}
