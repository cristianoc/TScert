// The walker of bounds-pattern-unreachable-field-refused in a module that
// also exports a class. Every export of a framed plan's component is a
// module function (docs/drafts/framed-acceptance.md, "Restrictions"): the
// initialization's last node is the array of the exports' closures, so the
// walker's framed plan is refused, and its ordinary plan is refused at the
// read after the visit.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

export class Origin {
  at(): number {
    return 0;
  }
}

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
