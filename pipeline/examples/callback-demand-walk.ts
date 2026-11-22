// Support-parametric callback demand: mutable array + local cursor.
// `walk` keeps `c.i` by local confinement and publishes a callback demand
// on `visit` preserving `xs`'s spine (`grow`). `sumAndTrace` discharges the
// demand because `visited` is allocated fresh (apart from `xs`).
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

export function sumAndTrace(xs: number[]): number {
  const visited: number[] = [];
  return walk(xs, (i) => {
    visited.push(i);
  });
}
