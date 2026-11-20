// A conditional of a literal and a parameter: where it yields the
// parameter, the write of `p.i` writes `c.i`, so no fact of `c.i` survives
// the write and the read is refused. Under Node, for three elements `c` is
// `p`, and the read is `xs[-1]`, `undefined` at `number`.
type C = { i: number };

export function conditional(xs: readonly number[], p: C): number {
  const c: C = xs.length > 3 ? { i: 0 } : p;
  c.i = 0;
  let total = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    const s = c.i;
    c.i = s;
    p.i = -1;
    const x: number = xs[c.i]!;
    total = total + x;
    c.i = s + 1;
  }
  return total;
}
