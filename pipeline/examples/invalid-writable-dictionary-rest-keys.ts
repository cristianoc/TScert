// An object pattern's rest owns none of the keys the pattern names, but a
// callee holding it as a writable dictionary may add one: `add` may store `x`.
// The rest is claimed as the dictionary alone, so a view saying `x` is
// absent, which would read the string `add` stored as a number, is not
// derived.
export function rest(
  add: (d: { [k: string]: string }) => void,
  s: { [k: string]: string },
): number | undefined {
  const { x: _, ...r } = s;
  add(r);
  const b: { x?: number } = r;
  return b.x;
}
