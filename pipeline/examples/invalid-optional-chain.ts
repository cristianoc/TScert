// The whole chain is `undefined` where the receiver is: `.b` is skipped with
// it, and the result is not a number.
function chained(x: { a: { b: number } } | undefined): number {
  // @ts-expect-error the chain is undefined where x is
  return x?.a.b;
}
