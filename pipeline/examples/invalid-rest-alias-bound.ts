// A rest parameter read through its alias's equation keeps the alias's
// bound.
type Args<T extends string> = [T];
export function f(...a: Args<number>): number {
  return a[0];
}
