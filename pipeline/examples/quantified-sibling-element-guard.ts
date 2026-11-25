type Row = { left: number[] | null; right: number[] | null };

/** @requires forall i in rows: rows[i].right === null || 1 <= rows[i].right.length */
export function countRows(rows: Row[]): number {
  return rows.length;
}

type NestedRow = { right: { items: number[] } | null };

/** @requires forall i in rows: rows[i].right === null || 1 <= rows[i].right.items.length */
export function countNestedRows(rows: NestedRow[]): number {
  return rows.length;
}
