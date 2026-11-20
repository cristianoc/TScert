// An object literal two constants hold, rebound to its copy by a key-adding
// write through the younger one, its field's facts stated at a loop's head:
// both constants hold the copy, so the write through the younger one writes
// the field and the read is refused. Under Node the read is `xs[-1]`,
// `undefined` at `number`.
type O = { i: number; j?: number };

export function alias(xs: readonly number[]): number {
  const c: O = { i: 0 };
  const o: O = c;
  let total = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    const s = c.i;
    c.i = s;
    o.j = s;
    o.i = -1;
    const x: number = xs[c.i]!;
    total = total + x;
    c.i = s + 1;
  }
  return total;
}
