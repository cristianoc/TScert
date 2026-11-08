// A comparison in a disjunction whose operand is not stated a safe integer.

/** @requires i < 0 || safeInteger(i) */
function at(xs: number[], i: number): number {
  return xs.length + i;
}

export function use(xs: number[]): number {
  return at(xs, 1);
}
