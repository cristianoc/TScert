// Temporaries whose last read is behind them leave the walk's state: the
// lengths `xs.length` read for the test, and the comparisons' Booleans once
// the branch is taken. The bound the test states stays on the names later
// nodes read: `i`, which the read link of `cursor.at` gives, so both element
// reads verify after the temporaries leave.
type Cursor = { at: number };
/** @requires safeInteger(cursor.at) */
export function twice(xs: number[], cursor: Cursor): number {
  const i = cursor.at;
  if (i < 0 || i >= xs.length) return 0;
  const w = xs[i]!;
  const sum = w + 1;
  return sum + xs[cursor.at]!;
}
