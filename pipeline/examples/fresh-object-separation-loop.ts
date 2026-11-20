// A fresh object a constant holds, its field's facts stated at a loop's
// head, then a write of another object's field in the body: the object's
// allocation separates its fields from the fields of every older value
// slot, the loop's head restates that separation, so the write keeps the
// facts. Pretext's walkPreparedLinesRaw: `cursor.segmentIndex = start`,
// `stats.lineCount++`, then a callee requiring the cursor's index.
type Cursor = { segmentIndex: number; graphemeIndex: number };
type Stats = { lineCount: number; maxLineWidth: number };

/** @requires safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
function step(cursor: Cursor): number {
  return cursor.segmentIndex;
}

export function walk(stats: Stats, xs: readonly number[]): number {
  const cursor: Cursor = { segmentIndex: 0, graphemeIndex: 0 };
  const count = xs.length;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < count) {
    const start = cursor.segmentIndex + 1;
    cursor.segmentIndex = start;
    stats.lineCount++;
    stats.maxLineWidth = step(cursor);
  }
  return stats.lineCount;
}

export function walkDefaulted(
  xs: readonly number[],
  stats: Stats = { lineCount: 0, maxLineWidth: 0 },
): number {
  const cursor: Cursor = { segmentIndex: 0, graphemeIndex: 0 };
  const count = xs.length;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < count) {
    const start = cursor.segmentIndex + 1;
    cursor.segmentIndex = start;
    stats.lineCount++;
    stats.maxLineWidth = step(cursor);
  }
  return stats.lineCount;
}
