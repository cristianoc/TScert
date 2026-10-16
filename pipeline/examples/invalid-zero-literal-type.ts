// After a test that `x` is not `0`, only the arm that is `0` remains, holding
// either zero; neither is `1`.
export function stillZero(x: 0 | 1): 1 {
  if (x !== 0) {
    return x;
  }
  return x;
}
