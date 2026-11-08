// Pretext normalizePreparedLineStart/countSteppedLines: a true return
// bounds the cursor written by the call.
/** @invariant safeInteger(this.index) && 0 <= this.index */
export type Cursor = { index: number };

/** @ensures result === false || safeInteger(cursor.index) && 0 <= cursor.index && cursor.index < xs.length */
export function advance(xs: number[], cursor: Cursor): boolean {
  const i = cursor.index;
  if (i < xs.length) {
    cursor.index = i;
    return true;
  }
  return false;
}

export function readAfterCall(xs: number[], cursor: Cursor): number {
  if (advance(xs, cursor)) return xs[cursor.index]!;
  return 0;
}

export function readAfterSavedCall(xs: number[], cursor: Cursor): number {
  const found = advance(xs, cursor);
  if (found) return xs[cursor.index]!;
  return 0;
}
