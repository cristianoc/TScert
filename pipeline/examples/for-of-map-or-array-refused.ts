// A `for...of` over a `Map` or an empty array: the iteration intrinsic is
// picked by one host kind, and the union of two has none. Stands for the
// loop over a guard's promises in `collect` (declaration-graph.mts), which
// iterates the `Map` itself where it is present.
export function promised(
  m: Map<string, Map<string, number>>,
  k: string,
): number {
  let n = 0;
  for (const [name, value] of m.get(k) ?? []) n += name.length + value;
  return n;
}
