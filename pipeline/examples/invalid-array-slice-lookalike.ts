// A method named `slice` of a program's own object is no array's: its
// result's length is unknown (run under Node: `at({ length: 1, slice: () =>
// [] }, 0)` returns `undefined`).
type Rows = { readonly length: number; slice(): number[] };
/** @requires safeInteger(i) && safeInteger(rows.length) && 0 <= i && i < rows.length */
export function at(rows: Rows, i: number): number {
  const copy = rows.slice();
  return copy[i]!;
}
