// The walker of bounds-pattern-unreachable-field in a module whose
// exported functions `even` and `odd` name each other. No module function
// of a framed plan's component names another
// (docs/drafts/framed-acceptance.md, "Restrictions"), so the walker's
// framed plan is refused at that gate, and its ordinary plan is refused at
// the read after the visit.
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

export function even(n: number): boolean {
  return n === 0 ? true : odd(n - 1);
}

export function odd(n: number): boolean {
  return n === 0 ? false : even(n - 1);
}
