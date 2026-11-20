// The walker of bounds-pattern-unreachable-field in a module with a
// `let` cell an exported function writes. Every outside slot of a framed
// plan's module function holds an audited realm value
// (docs/drafts/framed-acceptance.md, "Restrictions"): a module cell's
// contents vary with the depth of calls and no initialization of the
// component sets them, so the walker's framed plan is refused, and its
// ordinary plan is refused at the read after the visit.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

let visits: number = 0;

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

export function reset(): void {
  visits = 0;
}
