/** @requires safeInteger(i) && 0 <= i && i < rows.length
 *  @requires enabled === false || forall j in rows: 1 <= rows[j].length */
export function countRow(rows: number[][], i: number, enabled: boolean): number {
  const row = rows[i] ?? null;
  let total = 0;
  for (let k = 0; k < 2; k++) {
    if (enabled === true && row !== null) total += row[0]!;
  }
  return total;
}

/** @requires safeInteger(i) && 0 <= i && i < rows.length
 *  @requires enabled === false || forall j in rows: 1 <= rows[j].length */
export function countRowFirst(rows: number[][], i: number, enabled: boolean): number {
  const row = rows[i] ?? null;
  let total = 0;
  for (let k = 0; k < 2; k++) {
    if (row !== null && enabled === true) total += row[0]!;
  }
  return total;
}
