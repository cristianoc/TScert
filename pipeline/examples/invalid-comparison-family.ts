// Where `x === k` holds, `x` is one of `k`'s values, 0 or 1, not 1 alone.
export function f(x: number, k: 0 | 1): 1 {
  if (x === k) {
    return x;
  }
  return 1;
}
