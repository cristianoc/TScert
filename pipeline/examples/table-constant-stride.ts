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
