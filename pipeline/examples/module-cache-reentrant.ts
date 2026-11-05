// A module's own cache, a `Partial<Record<…>>` whose keys writes add
// (PROGRAM-TYPING.md, "Key-adding writes"): the right side of a write runs
// the cache's function again, at another key and then at its own key, before
// the outer write adds the key; the write's value is returned; another
// function reads the cache at `number[] | undefined`; a write as a statement
// (run under Node).
type Table = "a" | "b";
const cache: Partial<Record<Table, number[]>> = {};

function parse(table: Table): number[] {
  if (table === "b") {
    const first = rules("a");
    cache["b"] = [first.length];
    return [first.length + 1, 0];
  }
  return [1];
}

export function rules(table: Table): number[] {
  return cache[table] ?? (cache[table] = parse(table));
}

export function known(table: Table): number {
  const got = cache[table];
  return got === undefined ? -1 : got.length;
}

export function store(table: Table, rows: number[]): number {
  cache[table] = rows;
  return known(table);
}
