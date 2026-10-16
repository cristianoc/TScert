// An assignment in one arm of a conditional expression: the cell holds what
// either arm left.
function oneArm(flag: boolean): number {
  let state: number | null = null;
  const result = flag ? (state = 1) : 0;
  const n: number = state;
  return n + result;
}
