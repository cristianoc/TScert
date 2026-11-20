// The walker of bounds-pattern-unreachable-field creating a closure it
// calls and never gives out. The closure is lowered code its node
// expression creates, so the flow holds its token in O, its code open
// (docs/drafts/framed-acceptance.md, "Milestone 3"), and the slot of
// unused names its signature, the value of a creation naming the
// signature of its code: unused(0) is a known call. The walker's framed
// plan keeps the cursor facts at the visit, as P22's does.
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
