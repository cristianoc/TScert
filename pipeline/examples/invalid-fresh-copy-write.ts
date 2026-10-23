// A copy of a fresh object is the object: a write through the copy changes
// the field the original's test narrowed, which TypeScript still reads as a
// number. The returned value is null.
export function aliased(): number {
  const o: { value: number | null } = { value: 1 };
  if (o.value === null) return 0;
  const p = o;
  p.value = null;
  return o.value;
}
