type Row = { left: number[] | null; right: number[] | null };

/** @requires safeInteger(i) && 0 <= i && i < rows.length
 *  @requires forall j in rows: rows[j].left === null || 1 <= rows[j].right.length */
export function rightLength(rows: Row[], i: number): number {
  const row = rows[i]!;
  return row.left === null ? 0 : row.right!.length;
}
