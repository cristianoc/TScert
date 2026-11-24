// Two `Map` parameters may alias, so `b.set` (`b.size: scalar`) invalidates a
// bound read from `a.size` (run under Node: `const m = new Map();
// readAfterAliasSet(m, m, [42])` returns `undefined` at `number`).

/** @requires safeInteger(a.size) && 0 <= a.size && a.size < xs.length */
export function readAfterAliasSet(
  a: Map<string, number>,
  b: Map<string, number>,
  xs: number[],
): number {
  b.set("k", 1);
  return xs[a.size]!;
}
