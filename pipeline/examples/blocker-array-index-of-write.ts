// A write at the index indexOf finds for an element the array holds is a
// write at a key typed `number`, which has no rule: indexOf gives -1 for an
// element it does not find, and a write at or past the length extends the
// array, leaving holes below a later index.
// Census functions:
// host-families.mts#familyTable (avoided there, SOURCE-REWRITES.md).
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
