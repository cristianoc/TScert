// An element found in an array is updated in place: the entry for a name
// gathers each member stated under it, the first entry keeping its place.
// Census functions:
// host-families.mts#familyTable.
export function add(
  own: { name: string; members: number[] }[],
  name: string,
  m: number,
): void {
  const existing = own.find((f) => f.name === name);
  if (existing) existing.members.push(m);
  else own.push({ name, members: [m] });
}
