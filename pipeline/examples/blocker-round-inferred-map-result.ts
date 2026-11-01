// An unrestricted callback can shrink xs during the first map. Both maps
// retain the resulting hole, violating the Form[] result contract.
// Node counterexample: select([1, 2], read), with read closing over that
// same array and calling xs.pop() before returning { receiver: null }.
// The result has length 2, lacks index 1, and result[1].receiver throws.
// Census functions:
// declaration-graph.mts#selectGlobal
type Form = { receiver: string | null };
export function select(xs: number[], read: (x: number) => Form): Form[] {
  const forms = () => xs.map((x) => read(x));
  return forms().map((form) => ({ ...form, receiver: "self" }));
}
