// pretext's `normalizePreparedLineStart` steps its index in its loop's test,
// `if (++segmentIndex >= count) return 0`: an update nested in an expression
// keeps the binding in a cell (SourceFacts.lean, "Bindings held in cells"),
// which no index fact names, so the read `flags[segmentIndex]!` at the
// loop's next iteration has no bound and is refused. The program is safe;
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
