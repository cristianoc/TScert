// Pretext layoutNextRichInlineLineRange's start cursor: supplied and default values share a bound.
/** @requires safeInteger(cursor.index) && 0 <= cursor.index */
export function cursorIndex(cursor: { index: number } = { index: 0 }): number {
  return cursor.index;
}
export function entry(): number { return cursorIndex(); }
