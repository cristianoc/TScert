// `n && s` is `n` where `n` is 0, -0 or NaN.
function falsyNumber(n: number, s: string): string {
  return n && s;
}
