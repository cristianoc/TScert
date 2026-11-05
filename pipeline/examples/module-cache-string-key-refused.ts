// A module's own dictionary written at a `string` key: the key may be
// `__proto__`, whose setter the copy at string keys does not run, so the
// write is refused.
const cache: Record<string, number[]> = {};

export function rules(name: string): number[] {
  const known = cache[name];
  if (known !== undefined) return known;
  const made = [name.length];
  cache[name] = made;
  return made;
}
