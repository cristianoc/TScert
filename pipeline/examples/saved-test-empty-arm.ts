// A saved `typeof` test whose `if` has an empty arm: the lowered test has
// two exits into the same node, the true exit carrying the test's
// narrowing and the false exit none. The source for the single pass's
// forged-document control of the exits' order (dev/single-pass-agreement.mts):
// `x` read at the return is `string | number`, and a claim of `string`
// there is refused at the false exit (under Node `kept(1)` returns 1).
export function kept(x: string | number): string | number {
  const b = typeof x === "string";
  if (b) {
  }
  return x;
}
