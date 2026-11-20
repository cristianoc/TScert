// A cast of a parameter, `p as C`: the value is the parameter's, no
// allocation, so the write of `p.i` keeps no fact of `c.i` and the read is
// refused. Under Node `c` is `p`, and the read is `xs[-1]`, `undefined` at
// `number`.
type C = { i: number };

export function cast(xs: readonly number[], p: C): number {
  const c = p as C;
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
