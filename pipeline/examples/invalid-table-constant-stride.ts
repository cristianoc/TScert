// The row starts within the table; its last cell can be past the end.
// lastCell(new Uint8Array(28), 1) is undefined under Node.
/** @requires safeInteger(row) && 0 <= row && 28 * row <= table.length */
export function lastCell(table: Uint8Array, row: number): number {
  return table[row * 28 + 27]!;
}
