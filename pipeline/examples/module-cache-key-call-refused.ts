// A module's cache read at a key a call computes: the call may write the
// cache between the receiver's read and the read of the key, so the cache is
// not the module's own object, and its key-adding write is refused.
type Table = "a" | "b";
const cache: Partial<Record<Table, number[]>> = {};

function pick(table: Table): Table {
  return table;
}

export function rules(table: Table): number[] {
  return cache[pick(table)] ?? (cache[table] = [1]);
}
