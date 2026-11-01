// Array spread retains the native Map constructed for merge binders.
// Census functions:
// array-prototype.mts#mergeRefusal
export function entries<K, V>(binders: Map<K, V>): [K, V][] {
  return [...binders.entries()];
}
