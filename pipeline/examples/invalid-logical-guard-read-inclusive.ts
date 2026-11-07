// A read in the right operand of `&&` whose left operand admits the length:
// `e <= xs.length` lets `xs[e]!` read past the end. Under Node,
// `nonzeroPrefix([1, 2])` reads `xs[2]`, `undefined` at `number`.

export function nonzeroPrefix(xs: number[]): number {
  let e = 0;
  while (e <= xs.length && xs[e]! !== 0) e++;
  return e;
}
