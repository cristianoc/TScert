// A read bounded by another field of the same record: the clause bounds `i`
// by `row.widths.length`, the body reads `row.heights[i]!`, `undefined` at
// `number` past the heights' end (run under Node:
// `second({ widths: [1, 2], heights: [3] })` is `undefined`).
type Row = { widths: number[]; heights: number[] };

/** @requires safeInteger(i) && 0 <= i && i < row.widths.length */
function heightAt(row: Row, i: number): number {
  return row.heights[i]!;
}

export function second(row: Row): number {
  if (row.widths.length > 1) return heightAt(row, 1);
  return 0;
}
