// Array spread of a ReadonlyMap entries iterator.
// Census functions:
// array-prototype.mts#mergeRefusal
export function entries<K, V>(binders: ReadonlyMap<K, V>): [K, V][] {
  return [...binders.entries()];
}
