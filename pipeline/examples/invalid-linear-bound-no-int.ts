// The comparison alone does not make a plain number parameter a safe
// integer: `-1` passes `n < xs.length` and the write adds an own property no
// array owns (run under Node: `wrong([1,2,3], -1)` gives keys `0,1,2,-1`).
export function wrong(xs: number[], n: number): number[] {
  if (n < xs.length) xs[n] = 0;
  return xs;
}
