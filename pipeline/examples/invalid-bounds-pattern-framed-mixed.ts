// bounds-pattern-framed-mixed-local over the client's array: the visit's
// segment runs the arrow and the client's function, bounded by the top
// effect outside the component's region, where the client's array lies, so
// c.i < xs.length is dropped at the visit and the read after it is refused.
// Run under Node, total([1, 2, 3], g) with g popping the array reads past it
// (NaN, tests/node-runs.mts).
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

function walk(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 };
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    s += xs[c.i]!;
    c.i++;
  }
  return s;
}

export function total(xs: number[], g: () => void): number {
  return walk(xs, () => { g(); });
}
