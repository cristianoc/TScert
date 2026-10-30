// A `for...of` over a `ReadonlyMap`'s `values()` and a `ReadonlySet`'s
// `keys()`: a program's object may meet the view, so the overlay reads each
// as an `IterableIterator`, which the loop steps by the iterator protocol; a
// host `Map` meets the view through its native collection iterator, which
// is its own iterator. Stands for `exportsOf` in
// `declaration-graph.mts#collectDeclarations`, which iterates a symbol's
// member table.
export function total(m: ReadonlyMap<string, number>): number {
  let sum = 0;
  for (const v of m.values()) sum += v;
  return sum;
}

export function longest(s: ReadonlySet<string>): number {
  let n = 0;
  for (const w of s.keys()) if (w.length > n) n = w.length;
  return n;
}

export function counted(words: readonly string[]): number {
  const table = new Map<string, number>();
  for (const w of words) table.set(w, (table.get(w) ?? 0) + 1);
  return total(table) + longest(new Set(words));
}
