// A module's cache, created empty, whose key a logical assignment writes: it
// reads its receiver once, before its right side, which may replace the
// cache's object, so the cache is not the module's own object, and its
// key-adding write is refused.
type Table = "a" | "b";
const cache: Partial<Record<Table, number[]>> = {};

export function rules(table: Table): number[] {
  return cache[table] ?? (cache[table] = [1]);
}

export function reset(table: Table): void {
  cache[table] ??= [2];
}
