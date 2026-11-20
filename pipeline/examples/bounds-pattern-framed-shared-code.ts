// P22's walker (bounds-pattern-unreachable-field) twice, under two
// names.
//
// A code of the component is a term: `walk` and `walkAgain` have the same
// code, so they are one code of the component's flow of sites, with one
// pair of allocation sites per allocation and one closure token, and the
// initialization allocates a closure of that code for each of them. Each
// walker keeps `c.i < xs.length` across the call `visit(c.i)` as P22's
// does, and each is accepted under the client obligation of the component.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

export function walk(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 }; // never given to outside code
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i); // c.i unchanged; xs may only grow
    s += xs[c.i]!;
    c.i++;
  }
  return s;
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
  return s;
}
