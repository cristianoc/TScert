// An ordinary function field can shrink the searched array through an alias.
// Census functions:
// host-families.mts#familyTable
type Graph = { constantName: (t: number) => string | null };
export function find(
  graph: Graph,
  types: readonly number[],
  kind: string,
): number | undefined {
  return types.find((t) => graph.constantName(t) === kind);
}
