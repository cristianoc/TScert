// A descending pair cannot establish an ordered-array requirement.
/**
 * @requires forall i in xs: safeInteger(xs[i]) && 0 <= xs[i]
 * @requires forall i in xs: i + 1 >= xs.length || (safeInteger(xs[i]) && safeInteger(xs[i + 1]) && xs[i] <= xs[i + 1])
 */
function ordered(xs: number[], values: number[]): number {
  if (xs.length < 2 || xs[0]! <= xs[1]!) return 0;
  return values[values.length]! + 1;
}
export function descending(): number {
  const xs = [1, 0];
  return ordered(xs, [3]);
}
