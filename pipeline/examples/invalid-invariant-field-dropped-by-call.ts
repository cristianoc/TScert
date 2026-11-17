// A loop invariant on a field that a call in the body changes: `step`
// moves `c.i` two back, so the back edge does not establish `0 <= c.i`.
// Under Node `walk([1, 2], { i: 0 })` reads `xs[-1]` and returns `NaN`
// where every element read is claimed a number. The refusal names the
// invariant's facts the back edge lacks and the facts known there.
interface Cursor {
  i: number;
}
function step(c: Cursor): void {
  c.i = c.i - 2;
}
export function walk(xs: number[], c: Cursor): number {
  c.i = 0;
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length && c.i > -3) {
    s += xs[c.i]!;
    step(c);
    c.i = c.i + 1;
  }
  return s;
}
