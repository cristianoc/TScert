// A module-level cache filled at a key known only at run time, written as
// a `Map`: `get`, then on a miss the computed value, `set` and returned. It
// is the rewrite of the `Partial<Record<…>>` cache whose key-adding write
// the module's other references refuse (`blocker-pretext-module-cache-write`),
// as pretext's `graphemeRules` and `breakRules` hold their tables.
type Table = "a" | "b";
const cache = new Map<Table, number[]>();

function parse(table: Table): number[] {
  return table === "a" ? [1] : [2];
}

export function rules(table: Table): number[] {
  const known = cache.get(table);
  if (known !== undefined) return known;
  const made = parse(table);
  cache.set(table, made);
  return made;
}
