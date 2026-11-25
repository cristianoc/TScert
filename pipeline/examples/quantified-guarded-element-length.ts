// Guarded quantified element-length and parallel-array invariants
// (ARITHMETIC.md, "Quantified clauses"): each non-null entry of `advances`
// has length at least 1, and when `extras !== null` each non-null entry of
// `extras` is at least as long as the corresponding entry of `advances`.

/** @invariant this.extras === null || this.advances.length <= this.extras.length
 *  @invariant forall i in this.advances: this.advances[i] === null || 1 <= this.advances[i].length
 *  @invariant this.extras === null || forall i in this.advances: this.advances[i] === null || this.extras[i] === null || this.advances[i].length <= this.extras[i].length
 */
export type SegmentTable = {
  advances: (number[] | null)[];
  extras: (number[] | null)[] | null;
};

/** @requires safeInteger(i) && 0 <= i && i < table.advances.length */
export function lastAdvance(table: SegmentTable, i: number): number {
  const row = table.advances[i];
  if (row === undefined || row === null) return 0;
  return row[row.length - 1]!;
}

/** @requires safeInteger(i) && 0 <= i && i < table.advances.length */
export function sumWithExtras(table: SegmentTable, i: number): number {
  const { advances } = table;
  const row = advances[i];
  if (row === undefined || row === null) return 0;
  const extras = table.extras?.[i] ?? null;
  let total = 0;
  for (let g = 0; g < row.length; g++) {
    total += row[g]! + (extras === null ? 0 : extras[g]!);
  }
  return total;
}
