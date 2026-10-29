// Native weak tables: checked lookup, alias mutation, chaining and deletion.
export function lookup(key: object, other: object): number {
  const table = new WeakMap<object, number>();
  const alias = table.set(key, 7);
  const first = table.get(key);
  if (first === undefined) return 0;
  if (!table.has(key)) return 0;
  alias.delete(other);
  const again = table.get(key);
  return again === undefined ? 0 : first + again;
}
export function registered(thrown: unknown): number | undefined {
  const table = new WeakMap<object, number>();
  const key = {};
  table.set(key, 1);
  return thrown !== null && typeof thrown === "object"
    ? table.get(thrown)
    : undefined;
}
