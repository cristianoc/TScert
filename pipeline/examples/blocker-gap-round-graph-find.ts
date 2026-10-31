// find callback calling a function stored in a graph field.
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
