// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// graphemes.ts#findGraphemeEnds.
// Refusal: reject: source refusal: a write at a key known only at run time
// may add the key to an object another reference holds.
// A module-level cache, a `Partial<Record<…>>`, filled at a key known only
// at run time: a key-adding write is typed only on a local's own fresh
// object that nothing else has reached, and the module's object is reached
// by every call. The rewrite is a `Map`, `get` then `set` on a miss
// (`module-cache-map`).
type Table = "a" | "b";
const cache: Partial<Record<Table, number[]>> = {};

function parse(table: Table): number[] {
  return table === "a" ? [1] : [2];
}

export function rules(table: Table): number[] {
  return cache[table] ?? (cache[table] = parse(table));
}
