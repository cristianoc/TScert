// A method call on a union of primitives whose actual runs code: the saved
// head is the union of the primitives' members, each at its own receiver,
// and the call on the saved receiver has no rule.
function radix(): number {
  return 10;
}

export function text(x: number | bigint): string {
  return x.toString(radix());
}
