// The write back is at the cell's contract: `1 | 2` holds no number an
// increment gives.
export function step(): boolean {
  let x: 1 | 2 = 1;
  return x > 0 && x++ > 0;
}
