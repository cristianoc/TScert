// `typeof x !== "function"` keeps the primitive kinds of `unknown`, on which
// `in` throws a TypeError. Under Node, `probe(5)` throws.
export function probe(x: unknown): boolean {
  return typeof x !== "function" && "a" in x;
}
