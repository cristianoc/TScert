// A write of a key a module's own object states, whose right side calls: the
// call may add a key, replacing the object the write's receiver read, so the
// write is refused.
type Table = "a" | "b";
const cache: { hits: number; a?: number[]; b?: number[] } = { hits: 0 };

function fill(table: Table): number {
  cache[table] = [1];
  return 1;
}

export function count(table: Table): number {
  cache.hits = fill(table);
  return cache.hits;
}
