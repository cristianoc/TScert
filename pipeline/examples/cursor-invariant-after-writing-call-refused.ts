// pretext's line walkers step a cursor (`LayoutCursor`) through calls that
// write its fields. With the cursor's invariant `0 ≤ segmentIndex`, a safe
// integer, `step` meets it at its write and `read` assumes it, but the call
// of `read` after `step(cursor, …)` is refused: the call of `step` changes
// `cursor.segmentIndex`, and no fact of `step` states the invariant of its
// argument after the call, a precondition only (PROGRAM-TYPING.md, "Record
// invariants"). The program is safe. The producer derives, at the test of
// `step`, a fact whose bound is 2^53, past what the claims document states,
// and leaves it out.

/** @invariant safeInteger(this.segmentIndex) && 0 <= this.segmentIndex */
export type Cursor = { segmentIndex: number };

export function step(cursor: Cursor, count: number): void {
  if (cursor.segmentIndex + 1 < count) cursor.segmentIndex = cursor.segmentIndex + 1;
}

function read(cursor: Cursor): number {
  return cursor.segmentIndex;
}

export function stepped(flags: Uint8Array, cursor: Cursor): number {
  step(cursor, flags.length);
  return read(cursor);
}
