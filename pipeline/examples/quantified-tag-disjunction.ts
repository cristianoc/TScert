/** @requires forall i in xs: i < 0 || xs[i] === null */
export function countEmpty(xs: (number[] | null)[]): number {
  return xs.length;
}
