// A clause outside the language read: a disjunction of atoms.

/** @requires i < 0 || safeInteger(i) */
function at(xs: number[], i: number): number {
  return xs.length + i;
}

export function use(xs: number[]): number {
  return at(xs, 1);
}
