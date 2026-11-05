// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// graphemes.ts#findGraphemeEnds.
// A module-level cache, a `Partial<Record<…>>`, filled at a key known only
// at run time, the write's value returned: every mention of the cache is an
// access, so the module owns its object, and the key-adding write is the copy
// written to the cache's cell after the right side (PROGRAM-TYPING.md,
// "Key-adding writes").
type Table = "a" | "b";
const cache: Partial<Record<Table, number[]>> = {};

function parse(table: Table): number[] {
  return table === "a" ? [1] : [2];
}

export function rules(table: Table): number[] {
  return cache[table] ?? (cache[table] = parse(table));
}
