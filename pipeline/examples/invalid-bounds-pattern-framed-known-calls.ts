// bounds-pattern-framed-known-calls with the arrow moving the cursor: at the
// context of walk's known call the slot of visit holds the token of an
// arrow that captures total's cursor, so the cursor's site lies in the
// visit's reach and the arrow's write of c.i is charged there; c.i < xs.length
// is dropped at the visit and the read after it is refused. Run under Node,
// total([1, 2]) reads xs[2] (NaN, tests/node-runs.mts).
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

function walk(xs: number[], c: Cursor, visit: Visitor): number {
  c.i = 0;
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    s += xs[c.i]!;
    c.i++;
  }
  return s;
}

export function total(xs: number[]): number {
  const c: Cursor = { i: 0 };
  return walk(xs, c, () => { c.i = xs.length; });
}
