// A fact about a field of an object the walker allocated, across a callback
// that cannot reach it. The visitor's type states its effect,
// `Modifies<{ values: "any"; spines: "grow" }, void>`; it is given only a
// number, never the cursor `c`, so it cannot change `c.i`, and the read after
// the visit is within bounds (spines only grow). Safe.
// Gap: the stated effect covers every value location that exists at the
// call, `c.i` included, so `c.i < xs.length` is not kept across the visit; no
// rule bounds a callback's effect by the locations it can reach.
// Pretext: line-break.ts walkPreparedLinesRaw, countSteppedLines and
// walkPreparedComplexLines, which hold their index in a cursor object.
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
