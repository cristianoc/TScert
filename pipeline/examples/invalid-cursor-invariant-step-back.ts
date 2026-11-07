// A helper that steps the cursor back below 0 and returns: the cursor's
// invariant (`0 ≤ segmentIndex`) is a fact at the helper's returns, and its
// return does not establish it, so the helper is refused there. The caller
// then reads before the array's start (run under Node:
// `stepped({ widths: [1], segmentFlags: [1] }, { segmentIndex: 0 })` reads
// `undefined` at `number` at `i = -1`).

/** @invariant safeInteger(this.segmentIndex) && 0 <= this.segmentIndex */
export type Cursor = { segmentIndex: number };

/** @invariant this.segmentFlags.length === this.widths.length */
export type Prepared = { widths: number[]; segmentFlags: number[] };

function back(cursor: Cursor): void {
  cursor.segmentIndex = cursor.segmentIndex - 1;
}

export function stepped(prepared: Prepared, cursor: Cursor): number {
  back(cursor);
  const i = cursor.segmentIndex;
  return i < prepared.widths.length ? prepared.segmentFlags[i]! : 0;
}
