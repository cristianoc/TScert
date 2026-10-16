// The literal type `0` admits both runtime zeros: `-0` has type `0`, and
// strict equality equates the zeros. A parameter annotated with it is claimed
// at both, and a test against `0` keeps or removes both together.
export function zeroOrOne(x: 0 | 1): 0 | 1 {
  return x;
}
export function isZero(x: 0 | 1 | 2): 0 {
  if (x === 0) {
    return x;
  }
  return 0;
}
export function nonZero(x: 0 | 1 | 2): 1 | 2 {
  if (x !== 0) {
    return x;
  }
  return 1;
}
export function negativeZero(): 0 {
  return -0;
}
