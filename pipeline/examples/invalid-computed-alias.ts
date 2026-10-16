// An application of a computed alias is the type computed at its arguments:
// an element of an array of strings is a string.
type ElementOf<T extends readonly unknown[]> = T[number];
declare function first<E>(xs: readonly E[]): ElementOf<readonly E[]>;
export function bad(xs: readonly string[]): number {
  return first(xs);
}
