// Pretext's shouldBreakFast and nextBreakablePosition multiply a row by
// the fixed stride 28. The clause states the byte offset's bound.
/** @requires safeInteger(row) && 0 <= row && 28 * row + 27 < table.length */
export function lastCell(table: Uint8Array, row: number): number {
  return table[row * 28 + 27]!;
}

/** @requires safeInteger(row) && 0 <= row && 28 * row + 27 < table.length */
export function firstCell(table: Uint8Array, row: number): number {
  return table[28 * row]!;
}

/** @requires safeInteger(row) && -10 <= row && row <= 0 && 280 < table.length */
export function negativeStride(table: Uint8Array, row: number): number {
  return table[row * -28]!;
}

// Pretext's pair-table column is the code-unit offset divided by eight.
/** @requires safeInteger(row) && safeInteger(column) && 0 <= row && row <= 222 && 0 <= column && column <= 222 && 6244 <= table.length */
export function shiftedColumn(table: Uint8Array, row: number, column: number): number {
  const byte = column >> 3;
  return table[row * 28 + byte]!;
}

// Pretext's getClass selects the low byte of a Unicode code point.
/** @requires safeInteger(codePoint) && 0 <= codePoint && codePoint <= 1114111 && 256 <= table.length */
export function maskedColumn(table: Uint8Array, codePoint: number): number {
  const byte = codePoint & 255;
  return table[byte]!;
}
