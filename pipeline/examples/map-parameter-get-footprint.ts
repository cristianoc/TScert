// Census functions: fragment-statements.mts#functionDeclarations,#statements.
// A native `Map` parameter read by `get` inside a function stating
// `{value: any, store: grow}`: the standard `get` changes no location, so
// the function meets its statement.
export function placedBefore(
  placed: Map<string, number>,
  names: readonly string[],
  live: number,
): Modifies<{ values: "any"; stores: "grow" }, string[]> {
  const bound: string[] = [];
  for (const n of names) {
    const at = placed.get(n) ?? live;
    if (at < live) bound.push(n);
  }
  return bound;
}
