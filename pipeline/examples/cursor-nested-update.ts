// pretext's `normalizePreparedLineStart` steps its index in its loop's test,
// `if (++segmentIndex >= count) return 0`: no closure mentions the binding,
// so it is a slot the nested update rebinds (SOURCE-ELABORATION.md, "Slot or
// cell"), whose new value the linear facts state the old one plus one, so
// the test's false branch bounds it and the read `flags[segmentIndex]!` at
// the loop's next iteration is below the count;
// `cursor-invariant-loop-write` is the same loop with the update a statement.

/** @invariant safeInteger(this.segmentIndex) && 0 <= this.segmentIndex */
export type Cursor = { segmentIndex: number };

export function nextMarked(flags: Uint8Array, cursor: Cursor): number {
  const count = flags.length;
  let segmentIndex = cursor.segmentIndex;
  if (segmentIndex >= count) return 0;
  while (true) {
    const f = flags[segmentIndex]!;
    if (f === 1) {
      cursor.segmentIndex = segmentIndex;
      return f;
    }
    if (++segmentIndex >= count) return 0;
    cursor.segmentIndex = segmentIndex;
  }
}
