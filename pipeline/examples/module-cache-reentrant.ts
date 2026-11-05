// A module's own cache, a `Partial<Record<…>>` whose keys writes add
// (PROGRAM-TYPING.md, "Key-adding writes"): the right side of a write runs
// the cache's function again, at another key and then at its own key, before
// the outer write adds the key; the write's value is returned; another
// function reads the cache at `number[] | undefined`; a write as a statement,
// and one whose value a local holds; a right side that adds a key and then
// throws, the key kept; a closure reading and writing the cache (run under
// Node).
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

export function rulesHeld(table: Table): number[] {
  let rows = cache[table];
  if (rows === undefined) {
    rows = cache[table] = parse(table);
  }
  return rows;
}

function failing(table: Table): number[] {
  cache["a"] = [3, 3, 3];
  throw new Error(table);
}

export function attempt(table: Table): number {
  try {
    return (cache[table] = failing(table)).length;
  } catch {
    return known("a");
  }
}

export const lazy = (table: Table): number[] => cache[table] ?? (cache[table] = parse(table));
