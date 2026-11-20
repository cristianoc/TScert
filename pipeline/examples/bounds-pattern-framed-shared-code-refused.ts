// P22's walker (bounds-pattern-unreachable-field) twice, under two
// names, beside a module function both call. No module function of a
// framed plan's component names another (docs/drafts/framed-acceptance.md,
// "Restrictions"): each walker's capture of `total` is a linked capture,
// so each walker's framed plan is refused at that gate, and its ordinary
// plan is refused at the read after the visit.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

export function total(xs: number[]): number {
  let s = 0;
  for (let k = 0; k < xs.length; k++) s += xs[k]!;
  return s;
}

export function walk(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 }; // never given to outside code
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i); // c.i unchanged; xs may only grow
    s += xs[c.i]!;
    c.i++;
  }
  return s + total(xs);
}

export function walkAgain(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 }; // never given to outside code
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i); // c.i unchanged; xs may only grow
    s += xs[c.i]!;
    c.i++;
  }
  return s + total(xs);
}
