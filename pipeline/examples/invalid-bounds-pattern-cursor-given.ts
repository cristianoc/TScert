// The walker of bounds-pattern-unreachable-field-refused.ts, but the cursor
// is given to the visitor: the visitor may change `c.i` through its own
// alias, as its stated effect allows (`values: "any"`), so `c.i < xs.length`
// is lost at the visit, and the read `xs[c.i]` after it may be past the
// array. Under Node, `walk([1, 2, 3], (c) => { c.i = 5; })` reads `xs[5]`,
// `undefined`, and returns NaN (tests/node-runs.mts).
type Cursor = { i: number };
type Visitor = (c: Cursor) => Modifies<{ values: "any"; spines: "grow" }, void>;

export function walk(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 }; // given to outside code at each visit
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c);
    s += xs[c.i]!;
    c.i++;
  }
  return s;
}
