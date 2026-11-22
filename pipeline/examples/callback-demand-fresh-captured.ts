// Support-parametric callback demand discharged by a confined caller
// allocation: `visited` is captured by the visitor and by a second closure
// `keep`, which is stored into `h.onVisit` and so outlives the call. Calling
// `keep` only pushes to `visited`, so `visited` stays unreachable from `xs`,
// and the visitor's push leaves the walked spine unchanged.
type Visitor = (i: number) => void;
type Cursor = { i: number };

function walk(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 };
  let sum = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    sum += xs[c.i]!;
    c.i++;
  }
  return sum;
}

export function sumAndKeep(xs: number[], h: { onVisit: Visitor }): number {
  const visited: number[] = [];
  const keep: Visitor = (i) => {
    visited.push(i);
  };
  h.onVisit = keep;
  return walk(xs, (i) => {
    visited.push(i);
  });
}
