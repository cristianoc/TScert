// The walker of bounds-pattern-framed-inner-walker, its visitor an arrow a
// module function makes, which does nothing. No node of the component may
// call outside code, so the visit is bounded by its segment's charges, and
// the cursor's site lies outside the visit's reach: c.i < xs.length is kept.
// The bound reads the arrow's code as lowered, so walk's verdict rests on
// mk's, which is verified; total rests on walk's.
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

function mk(): Visitor {
  return (w: number) => {};
}

export function total(xs: number[]): number {
  return walk(xs, mk());
}
