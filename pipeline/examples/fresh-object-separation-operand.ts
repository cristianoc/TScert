// An initializer whose value is one of its operands', each operand an
// object literal: `{ i: 0 } as C`, and a conditional of two literals. The
// value is fresh, so the constant's field facts stated at a loop's head
// survive a write of a parameter's field in the body.
type C = { i: number };

export function cast(xs: readonly number[], p: C): number {
  const c = { i: 0 } as C;
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

export function conditional(xs: readonly number[], p: C): number {
  const c: C = xs.length > 3 ? { i: 0 } : { i: 1 };
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
