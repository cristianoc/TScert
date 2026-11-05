// A module's cache whose member an update writes: an update reads its
// receiver once, before its right side, which may replace the cache's
// object, so the cache is not the module's own object, and its key-adding
// write is refused.
type Table = "a" | "b";
const cache: { hits: number; a?: number[]; b?: number[] } = { hits: 0 };

export function rules(table: Table): number[] {
  cache.hits += 1;
  return cache[table] ?? (cache[table] = [1]);
}
