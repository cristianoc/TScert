// `Set.prototype.add` writes `this.size` at `scalar`, so a bound read from
// `s.size` before `s.add` does not survive the mutation (run under Node:
// `readAfterSetAdd(new Set(), [42])` returns `undefined` at `number`).

/** @requires safeInteger(s.size) && 0 <= s.size && s.size < xs.length */
export function readAfterSetAdd(s: Set<string>, xs: number[]): number {
  s.add("k");
  return xs[s.size]!;
}
