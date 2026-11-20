// The walker of bounds-pattern-unreachable-field-refused beside an exported
// function collecting a rest parameter. No code of a framed plan's
// component collects a rest (docs/drafts/framed-acceptance.md,
// "Restrictions"): a closure with a rest is entered at its rest's binding,
// where the entering state bounds the run's slots from below alone, so the
// walker's framed plan is refused, and its ordinary plan is refused at the
// read after the visit.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

export function walk(xs: number[], visit: Visitor): number {
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

export function count(...ws: number[]): number {
  return ws.length;
}
