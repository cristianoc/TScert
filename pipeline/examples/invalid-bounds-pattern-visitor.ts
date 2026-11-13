// Bounds pattern P1, the unsafe neighbour of `bounds-pattern-visitor-refused`:
// the walker called with a visitor that empties the array, so the read after
// the walk is past the end (run under Node: NaN). An effect variable for the
// visitor must take this visitor's effect, which changes stores.
type Visitor = (w: number) => void;

function walk(xs: number[], visit: Visitor | undefined): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    s += xs[i]!;
    if (visit !== undefined) visit(s);
  }
  return s;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function emptied(xs: number[], i: number): number {
  const w = walk(xs, () => {
    while (xs.length > 0) xs.pop();
  });
  return w + xs[i]!;
}
