// `Map.prototype.set` writes `this.size` at `scalar`, so a bound read from
// `m.size` before `m.set` does not survive the mutation (run under Node:
// `readAfterMapSet(new Map(), [42])` returns `undefined` at `number`).

/** @requires safeInteger(m.size) && 0 <= m.size && m.size < xs.length */
export function readAfterMapSet(m: Map<string, number>, xs: number[]): number {
  m.set("k", 1);
  return xs[m.size]!;
}
