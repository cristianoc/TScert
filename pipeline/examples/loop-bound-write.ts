// A write in a loop body at an index the loop's test bounds: the loop head's
// claimed knowledge states no facts, so the comparison inside the loop
// states none and the write's bound is not derived.
export function clear(xs: number[]): void {
  for (let j = 0; j < xs.length; j++) {
    xs[j] = 0;
  }
}
