// pretext's `PreparedLineBreakData` holds its flags in a `Uint8Array`, and
// its invariant equates the view's length with `widths.length`. A
// helper receiving the record and a cursor states the record's invariant at
// its returns after writing `cursor.segmentIndex`, a number field: the write
// keeps the field `segmentFlags` (it alters no object), and the typed-array length
// of the view the field holds is read from a location its type states stable,
// so the length read through the field is preserved (`view-path-stable`). A bound
// read through the field is preserved across the same write.

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

export function flagAfterStep(prepared: Prepared, cursor: Cursor): number {
  const i = cursor.segmentIndex;
  if (i < prepared.segmentFlags.length) {
    cursor.segmentIndex = i + 1;
    return prepared.segmentFlags[i]!;
  }
  return 0;
}
