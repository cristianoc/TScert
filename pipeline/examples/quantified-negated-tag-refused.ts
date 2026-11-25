/** @requires forall i in xs: xs[i] !== null */
export function countPresent(xs: (number[] | null)[]): number {
  return xs.length;
}
