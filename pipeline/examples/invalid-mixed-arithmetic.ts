// Arithmetic mixing a bigint and a number: refused, as TypeScript refuses
// it. It would throw a TypeError, an outcome, but it is almost surely a bug.
function mix(a: bigint, b: number): bigint {
  return a + b;
}
