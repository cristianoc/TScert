/** @requires forall 1 + 1 <= i in xs: xs[i] === null */
export function countTail(xs: (number[] | null)[]): number {
  return xs.length;
}
