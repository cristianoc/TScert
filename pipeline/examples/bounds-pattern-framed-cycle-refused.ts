// The walker of bounds-pattern-unreachable-field in a module whose
// exported functions `even` and `odd` name each other. A framed plan's
// component has an acyclic name graph among its module functions
// (docs/drafts/framed-acceptance.md, "Restrictions"): the closures of two
// functions naming each other have no finite initialization, so the
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

export function even(n: number): boolean {
  return n === 0 ? true : odd(n - 1);
}

export function odd(n: number): boolean {
  return n === 0 ? false : even(n - 1);
}
