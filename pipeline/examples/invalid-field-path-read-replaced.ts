// A field replaced between the test and the read: the caller tests
// `row.widths.length`, replaces `row.widths` with an empty array, then calls
// the reader at index 0, `undefined` at `number` (run under Node:
// `replaced({ widths: [1] })` is `undefined`).
type Row = { widths: number[] };

/** @requires safeInteger(i) && 0 <= i && i < row.widths.length */
function widthAt(row: Row, i: number): number {
  return row.widths[i]!;
}

export function replaced(row: Row): number {
  if (row.widths.length > 0) {
    row.widths = [];
    return widthAt(row, 0);
  }
  return 0;
}
