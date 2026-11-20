// A fresh object a constant holds, its field's facts stated at a loop's
// head, and an older `let` the body assigns the object to: from the second
// iteration on, the write through the `let` writes the object's field, so
// the loop's head restates no separation from the `let`'s fields and the
// read `xs[cursor.segmentIndex]!` is refused. Under Node the second
// iteration reads `xs[-1]`, `undefined` at `number`.
type Cursor = { segmentIndex: number };

export function aliased(xs: readonly number[]): number {
  let target: Cursor = { segmentIndex: 0 };
  const cursor: Cursor = { segmentIndex: 0 };
  let total = 0;
  /** @invariant safeInteger(cursor.segmentIndex) && 0 <= cursor.segmentIndex */
  while (cursor.segmentIndex < xs.length) {
    const start = cursor.segmentIndex;
    cursor.segmentIndex = start;
    target.segmentIndex = -1;
    const x: number = xs[cursor.segmentIndex]!;
    total = total + x;
    target = cursor;
    cursor.segmentIndex = start + 1;
  }
  return total;
}
