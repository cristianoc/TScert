// A mapped array used as a some receiver.
// Census functions:
// declaration-graph.mts#collect
type Item = { optional: boolean };
export function optional(xs: number[], read: (x: number) => Item): boolean {
  const mapped = xs.map((x) => read(x));
  return mapped.some((x) => x.optional);
}
