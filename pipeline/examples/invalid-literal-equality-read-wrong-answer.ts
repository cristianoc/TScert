// A read on the answer a literal comparison does not bound: `i !== 0 ||`
// runs its right operand where `i` is `0`, so `xs[i - 1]!` reads `xs[-1]`.
// Under Node, `firstOrPrevious([1, 2], 0)` reads `undefined` at `number`.

/** @requires safeInteger(i) && 0 <= i && i <= xs.length */
export function firstOrPrevious(xs: number[], i: number): boolean {
  return i !== 0 || xs[i - 1]! > 0;
}
