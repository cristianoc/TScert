// A `Set<T>` is a `ReadonlySet<T>` and a `Map<K, V>` a `ReadonlyMap<K, V>`:
// the readers' views of the host's collections, passed directly, held in a
// defaulted parameter beside a fresh collection, and spread or iterated
// through the iterator protocol, as `type-term.mts#visitType` holds its
// bound names.
export function size(bound: ReadonlySet<string> = new Set()): number {
  return bound.size;
}

export function merged(
  more: readonly string[],
  bound: ReadonlySet<string> = new Set(),
): number {
  return new Set([...bound, ...more]).size;
}

export function scoped(more: readonly string[]): number {
  const inner = new Set(more);
  return size(inner) + merged(more, inner);
}

export function keys(table: ReadonlyMap<string, number>): string[] {
  const out: string[] = [];
  for (const [key, value] of table)
    if (table.get(key) === value && table.has(key)) out.push(key);
  return out;
}

export function counted(words: readonly string[]): string[] {
  const table = new Map<string, number>();
  for (const w of words) table.set(w, (table.get(w) ?? 0) + 1);
  return keys(table);
}
