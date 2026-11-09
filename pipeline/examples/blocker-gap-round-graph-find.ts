// find callback calling a function stored in a graph field.
// Census functions:
// host-families.mts#familyTable
type Graph = {
  constantName: (t: number) => Modifies<{}, string | null>;
};
export function find(
  graph: Graph,
  types: readonly number[],
  kind: string,
): number | undefined {
  return types.find((t) => graph.constantName(t) === kind);
}

// The graph supplies a lookup over saved constants, as the declaration reader does.
export function lookupGraph(
  constants: readonly { value: number; name: string }[],
): Graph {
  return {
    constantName: (value): Modifies<{}, string> =>
      constants.find((c) => c.value === value)?.name ?? String(value),
  };
}
