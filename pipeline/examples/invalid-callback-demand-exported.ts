// Negative case for exported callback demand: `walk` is exported with an
// unannotated callback parameter, so unanalyzed external callers may pass a
// callback that pops `xs` (NaN under Node). The verifier refuses to accept
// an exported function by silently assuming an unstated callback demand.
type Visitor = (i: number) => void;
type Cursor = { i: number };

export function walk(xs: number[], visit: Visitor): number {
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
