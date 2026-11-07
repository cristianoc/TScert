// Parentheses around `new Array<T>(n)` before its `.fill(v)` are transparent:
// TypeScript gives the wrapped and the direct form one meaning, so the
// construct is read as `fill`'s receiver and the call as the filling
// intrinsic, exactly as written directly
// (SOURCE-CONTRACTS.md, "`new Array` filled at once").
export function zeros(n: number): number[] {
  // prettier-ignore
  return (new Array<number>(n)).fill(0);
}
