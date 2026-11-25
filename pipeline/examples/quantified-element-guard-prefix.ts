/** @requires chunks.length <= extras.length
 *  @requires forall j in extras: extras[j] === null || 1 <= 0
 *  @ensures forall j in chunks: result[j] === null || chunks[j] === null || chunks[j].length <= result[j].length */
export function keepNullExtras(
  chunks: (number[] | null)[],
  extras: (number[] | null)[],
): (number[] | null)[] {
  return extras;
}

/** @requires 0 <= rows.length
 *  @requires forall j in rows: rows[j] === null || 1 <= 0
 *  @ensures forall j in result: result[j] === null || 2 <= result[j].length */
export function keepNullRows(rows: (number[] | null)[]): (number[] | null)[] {
  return rows;
}

export type Row = { tail: number[] | null };

/** @requires 0 <= rows.length
 *  @requires forall j in rows: rows[j].tail === null || 1 <= 0
 *  @ensures forall j in rows: rows[j].tail === null || 2 <= rows[j].tail.length */
export function keepNullTails(rows: Row[]): Row[] {
  return rows;
}

/** @requires chunks.length <= rows.length
 *  @requires forall j in rows: rows[j].tail === null || 1 <= 0
 *  @ensures forall j in chunks: chunks[j] === null || result[j].tail === null || chunks[j].length <= result[j].tail.length */
export function keepNullParallelTails(
  chunks: (number[] | null)[],
  rows: Row[],
): Row[] {
  return rows;
}
