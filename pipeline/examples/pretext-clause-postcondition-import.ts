// Pretext countSteppedLines: a checked module helper's Boolean postcondition.
import { advance, type Cursor } from "./pretext-clause-postcondition.js";

export function readAfterImportedCall(xs: number[], cursor: Cursor): number {
  if (advance(xs, cursor)) return xs[cursor.index]!;
  return 0;
}
