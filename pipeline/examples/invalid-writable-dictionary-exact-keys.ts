// A fresh literal owns exactly its written keys, but a callee holding it as a
// writable dictionary may add one: `add` may store `x`. The literal's exact
// keys are not claimed once it is passed, so a view saying `x` is absent,
// which would read the string `add` stored as a number, is not derived.
export function exact(
  add: (d: { [k: string]: string }) => void,
): number | undefined {
  const o = {};
  add(o);
  const b: { x?: number } = o;
  return b.x;
}
