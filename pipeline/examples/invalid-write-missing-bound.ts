// A write of an element at an index the precondition does not bound by the
// array's length: under Node `w([], 5)` leaves `xs` with five holes, where
// `number[]` states every element present. The refusal names the bound the
// write requires, `index(i) && i <= xs.length`, and the facts known over
// the operands.
/** @requires safeInteger(i) && 0 <= i */
export function w(xs: number[], i: number): void {
  xs[i] = 1;
}
