// A cursor stepped through a typed array's segments, pretext's
// `normalizePreparedLineStart` with its update a statement of its own: the
// cursor's invariant (`0 ≤ segmentIndex`, a safe integer) bounds the index
// read from it, and the writes of `cursor.segmentIndex` in the loop keep the
// facts over `flags`, whose element count is stable. From the invariant's
// `segmentIndex ≤ 2^53 − 1` the producer derives after `segmentIndex++` a
// fact whose bound is 2^53, past what the claims document states, and leaves
// it out, a weaker claim.

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
    segmentIndex++;
    if (segmentIndex >= count) return 0;
    cursor.segmentIndex = segmentIndex;
  }
}
