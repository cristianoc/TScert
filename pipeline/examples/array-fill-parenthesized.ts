// The restriction of `new Array<T>(n).fill(v)` to its written form: the
// construct parenthesized before its `fill` is safe, but is read as the
// construct alone, which makes holes, and refused
// (SOURCE-CONTRACTS.md, "`new Array` filled at once").
export function zeros(n: number): number[] {
  // prettier-ignore
  return (new Array<number>(n)).fill(0);
}
