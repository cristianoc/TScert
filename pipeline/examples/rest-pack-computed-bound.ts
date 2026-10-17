// A rest pack bounded by a computed alias's application: the bound is what
// TypeScript computes, `string[]`, an array bound, and the application is
// within its own bound.
type Element<T extends readonly unknown[]> = T[number];
export function f<T extends Element<string[][]>>(...x: T): number {
  return 1;
}
