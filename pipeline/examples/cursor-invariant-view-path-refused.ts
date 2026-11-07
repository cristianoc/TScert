// pretext's `PreparedLineBreakData` holds its flags in a `Uint8Array`, and
// its invariant equates the view's element count with `widths.length`. A
// helper receiving the record and a cursor states the record's invariant at
// its returns, but its write of `cursor.segmentIndex`, a number field, may
// alter any location holding a number, and the element count of a view read
// through a path is such a location: no rule states the view's count kept
// where its object is read through a field, and the return is refused. The
// program is safe; `cursor-invariant-after-writing-call` is the same helper
// over an array of flags.

/** @invariant safeInteger(this.segmentIndex) && 0 <= this.segmentIndex */
export type Cursor = { segmentIndex: number };

/** @invariant this.segmentFlags.length === this.widths.length */
export type Prepared = { widths: number[]; segmentFlags: Uint8Array };

export function step(prepared: Prepared, cursor: Cursor): boolean {
  const segmentIndex = cursor.segmentIndex;
  if (segmentIndex < prepared.widths.length - 1) {
    cursor.segmentIndex = segmentIndex + 1;
    return true;
  }
  return false;
}
