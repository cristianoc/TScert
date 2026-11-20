// An object literal a constant holds, its field's facts stated at a loop's
// head, and a younger constant bound to the same object: the younger
// constant is no value bound before the allocation, so the write through it
// keeps no fact of the object's field and the read is refused. Under Node
// the read is `xs[-1]`, `undefined` at `number`.
type C = { i: number };

export function alias(xs: readonly number[]): number {
  const c: C = { i: 0 };
  const o: C = c;
  let total = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    const s = c.i;
    c.i = s;
    o.i = -1;
    const x: number = xs[c.i]!;
    total = total + x;
    c.i = s + 1;
  }
  return total;
}
