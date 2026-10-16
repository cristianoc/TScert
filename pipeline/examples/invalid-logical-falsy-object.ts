// `o && o.a` is `undefined` where `o` is.
function falsyLeft(o: { a: number } | undefined): number {
  return o && o.a;
}
