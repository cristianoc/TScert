// A field read twice with no write between gives one value: the read link
// the first read of `cursor.at` states says the field holds its value, so the
// second read's result is that value's name, and the bound the test states of
// the first read holds of the index the second read gives.
type Cursor = { at: number };
/** @requires safeInteger(cursor.at) */
export function pair(xs: number[], cursor: Cursor): number {
  const first = cursor.at;
  if (first < 0 || first >= xs.length) return 0;
  return xs[cursor.at]!;
}
