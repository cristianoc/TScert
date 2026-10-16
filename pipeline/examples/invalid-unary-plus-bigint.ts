// Unary `+` on a bigint throws a TypeError: refused.
function toNumber(x: bigint): number {
  return +x;
}
