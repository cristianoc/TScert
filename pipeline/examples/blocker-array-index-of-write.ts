// A write at the index indexOf found for an element the array holds needs
// that index proved an array index: indexOf returns -1 for an element it
// does not find.
// Census functions:
// host-families.mts#familyTable.
export function add(
  own: { name: string; members: number[] }[],
  name: string,
  m: number,
): void {
  const existing = own.find((f) => f.name === name);
  if (existing)
    own[own.indexOf(existing)] = {
      ...existing,
      members: [...existing.members, m],
    };
}
