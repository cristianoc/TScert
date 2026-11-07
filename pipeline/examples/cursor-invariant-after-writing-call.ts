// pretext's `countSteppedLines` steps a cursor (`LayoutCursor`) through a
// call that writes its fields, then reads the flags at the cursor's index.
// `step` writes no binding of its parameters, so each parameter's invariant
// is also a fact at its returns (PROGRAM-TYPING.md, "Record invariants"):
// each call states `0 ≤ cursor.segmentIndex`, a safe integer, and the
// record's invariant again, and the read `segmentFlags[cursor.segmentIndex]!`
// below `segmentCount` is bounded by them and by `segmentCount =
// segmentFlags.length`, derived before the loop over the bindings alone. A
// write of a field the receiver's type states gives the field's new value
// (`write-link`), so `step`'s `return true` meets the cursor's invariant
// from `segmentIndex + 1`. The flags are an array; `cursor-invariant-view-path`
// is the same helper over a `Uint8Array`.

/** @invariant safeInteger(this.segmentIndex) && 0 <= this.segmentIndex */
export type Cursor = { segmentIndex: number };

/** @invariant this.segmentFlags.length === this.widths.length */
export type Prepared = { widths: number[]; segmentFlags: number[] };

function step(prepared: Prepared, cursor: Cursor): boolean {
  const segmentIndex = cursor.segmentIndex;
  if (segmentIndex < prepared.widths.length - 1) {
    cursor.segmentIndex = segmentIndex + 1;
    return true;
  }
  return false;
}

export function countMarked(prepared: Prepared): number {
  const { segmentFlags } = prepared;
  const segmentCount = prepared.widths.length;
  const cursor: Cursor = { segmentIndex: 0 };
  let count = 0;
  while (step(prepared, cursor)) {
    if (cursor.segmentIndex < segmentCount && segmentFlags[cursor.segmentIndex]! !== 0) count++;
  }
  return count;
}

export function stepped(prepared: Prepared, cursor: Cursor): number {
  step(prepared, cursor);
  const i = cursor.segmentIndex;
  return i < prepared.widths.length ? prepared.segmentFlags[i]! : 0;
}
