// A call that may shorten a store keeps no bound of a length, in a
// declaration as in a statement of its own (run under Node:
// `declared([5], 0)` returns `NaN`).
function drop(xs: number[]): number {
  xs.pop();
  return xs.length;
}

/** @requires safeInteger(i) && 0 <= i && i < xs.length */
export function declared(xs: number[], i: number): number {
  const n = drop(xs);
  return xs[i]! + n;
}
