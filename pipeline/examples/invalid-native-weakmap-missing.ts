// has does not make a later get present: an alias can delete the entry.
export function wrong(key: object): number {
  const table = new WeakMap<object, number>();
  const alias = table;
  table.set(key, 1);
  if (table.has(key)) {
    alias.delete(key);
    return table.get(key);
  }
  return 0;
}
