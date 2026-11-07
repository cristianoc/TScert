// Parentheses are transparent but an optional chain is not: the reviewed
// form is a plain read of `fill` on the construct, so the optional read is
// refused and the construct is read alone, which makes holes
// (SOURCE-CONTRACTS.md, "`new Array` filled at once").
export function zeros(n: number): number[] {
  // prettier-ignore
  return (new Array<number>(n))?.fill(0);
}
