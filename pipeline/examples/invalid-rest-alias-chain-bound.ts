// A rest parameter read through a chain of aliases keeps the bound of the
// application written.
type Inner<T extends string> = [T];
type Outer<T extends string> = Inner<T>;
export function f(...a: Outer<number>): number {
  return a[0];
}
