// A write of a number to a field of type number is a scalar's step: its old
// and new contents are neither objects nor spines, so `c.i = j` is within
// `{ values: "scalar" }` and its postcondition holds at the return.
type Cursor = { i: number };

/** @requires safeInteger(j)
 * @ensures safeInteger(c.i) && c.i === j */
export function moveTo(c: Cursor, j: number): Modifies<{ values: "scalar" }, void> {
  c.i = j;
}
