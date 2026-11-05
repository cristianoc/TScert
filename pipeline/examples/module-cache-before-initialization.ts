// A module's own cache written before its declaration runs: the write reads
// the cache's binding first, as JavaScript does, so the ReferenceError comes
// before the right side runs (`before` is 0); after the declaration the
// write adds the key (`after` is 1). Run under Node.
type Table = "a" | "b";
let effects: number = 0;

function rhs(): number[] {
  effects = effects + 1;
  return [effects];
}

function fill(table: Table): number[] {
  return (cache[table] = rhs());
}

function attempt(): number {
  try {
    fill("a");
  } catch {
    return effects;
  }
  return -1;
}

export const before: number = attempt();
const cache: Partial<Record<Table, number[]>> = {};
export const after: number = fill("b").length;
