// Bounds pattern P20: a type invariant of a value read back from a `Map`.
// Fact: t.index.length === 4352 for the value `cache.get(name)` returns.
// Pretext: line-breaks.ts markRuleBoundaries (1 site, and getClass's
// precondition at its callers).
// Gap: a type invariant is a boundary contract; a value read from a native's
// result carries none, so `tableOf`'s return does not establish it.
/** @invariant this.index.length === 4352 */
export type ClassTable = { readonly index: Uint16Array };

function build(): ClassTable {
  const index = new Uint16Array(4352);
  return { index };
}

const cache = new Map<string, ClassTable>();

function tableOf(name: string): ClassTable {
  let t = cache.get(name);
  if (t === undefined) {
    t = build();
    cache.set(name, t);
  }
  return t;
}

/** @requires safeInteger(c) && 0 <= c && c < 1114112 */
export function classOf(name: string, c: number): number {
  return tableOf(name).index[c >> 8]!;
}
