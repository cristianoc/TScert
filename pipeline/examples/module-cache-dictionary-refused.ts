// A module's own dictionary written at a `string` key: its type states no
// finite key set, so its key-adding write is refused.
const cache: Record<string, number[]> = {};

export function rules(name: string): number[] {
  const known = cache[name];
  if (known !== undefined) return known;
  const made = [name.length];
  cache[name] = made;
  return made;
}
