// The helper returns true at an index equal to the length.
/** @invariant safeInteger(this.index) && 0 <= this.index */
export type Cursor = { index: number };

/** @ensures result === false || safeInteger(cursor.index) && 0 <= cursor.index && cursor.index < xs.length */
export function advance(xs: number[], cursor: Cursor): boolean {
  cursor.index = xs.length;
  return true;
}

export function unsafe(xs: number[], cursor: Cursor): number {
  if (advance(xs, cursor)) return xs[cursor.index]! + 1;
  return 0;
}
