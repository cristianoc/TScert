// An inferred function result from map used as another map receiver.
// Census functions:
// declaration-graph.mts#selectGlobal
type Form = { receiver: string | null };
export function select(xs: number[], read: (x: number) => Form): Form[] {
  const forms = () => xs.map((x) => read(x));
  return forms().map((form) => ({ ...form, receiver: "self" }));
}
