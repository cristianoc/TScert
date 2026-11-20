// The walker of bounds-pattern-unreachable-field creating a closure it
// never calls or gives out. No module function of a framed plan's
// component creates a closure (docs/drafts/framed-acceptance.md,
// "Restrictions"), so the walker's framed plan is refused at that gate,
// and its ordinary plan is refused at the read after the visit.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

export function walk(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 };
  let s = 0;
  const unused = (n: number): number => n;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    s += xs[c.i]!;
    c.i++;
  }
  return s + unused(0);
}
