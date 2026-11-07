// A read in the right operand of `||` after a strict inequality: its `false`
// answer is `e === xs.length`, so `xs[e]!` reads at the length. Under Node,
// `notEndOrZero([1, 2], 2)` reads `xs[2]`, `undefined` at `number`.

/** @requires safeInteger(e) && 0 <= e && e <= xs.length */
export function notEndOrZero(xs: number[], e: number): boolean {
  return e !== xs.length || xs[e]! === 0;
}
