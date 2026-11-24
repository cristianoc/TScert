// A field read again after a write that reaches it: the write moves
// `cursor.at` past the end of `xs`, so the second read gives another value,
// which the test before the write does not bound, and the element read
// gives `undefined` for a number (run under Node: NaN).
type Cursor = { at: number };
/** @requires safeInteger(cursor.at) */
export function pair(xs: number[], cursor: Cursor): number {
  const first = cursor.at;
  if (first < 0 || first >= xs.length) return 0;
  cursor.at = xs.length;
  return first + xs[cursor.at]!;
}
