// The callback writes a cell of the enclosing function: not fresh for the
// callback, yet disjoint from everything map reads. Safe.
export function runningTotals(xs: readonly number[]): number[] {
  let total = 0;
  return xs.map((x: number): number => {
    total = total + x;
    return total;
  });
}
