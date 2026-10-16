// `x` is assigned on one path only: where `flag` is false the read gives
// `undefined`, not a number.
function readBeforeAssignment(flag: boolean): number {
  let x: number;
  if (flag) {
    x = 1;
  }
  return x;
}
