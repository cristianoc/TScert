// `typeof x === "object"` also holds for null, on which `in` throws a
// TypeError. Under Node, `probe(null)` throws.
export function probe(x: unknown): boolean {
  return typeof x === "object" && "a" in x;
}
