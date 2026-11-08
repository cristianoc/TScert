// pretext's `normalizePreparedLineStart` steps its index in its loop's test,
// `if (++segmentIndex >= count) return 0`: an update nested in an expression
// keeps the binding in a cell (SourceFacts.lean, "Bindings held in cells"),
// whose value the linear facts name as the path `value` of the cell
// (PROGRAM-TYPING.md, "Terms for bindings held in cells"), so the test's
// false answer bounds the stored value and the read `flags[segmentIndex]!`
// at the loop's next iteration is below the count;
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
