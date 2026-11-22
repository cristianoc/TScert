// Negative case for support-parametric callback demand: `sumAndAlias` passes
// a callback that pops from `xs`, violating `walk`'s spine-preservation demand.
// Unsafe under Node: `sumAndAlias([1, 2])` reads past `xs` (`xs[1]` is undefined).
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

export function sumAndAlias(xs: number[]): number {
  return walk(xs, (_i) => {
    xs.pop();
  });
}
