// A read in the right operand of `||` bounded only on the answer that skips
// it: `e < xs.length || xs[e]! > 0` reads where `e` is at least the length.
// Under Node, `pastOrPositive([1, 2], 2)` reads `xs[2]`, `undefined` at
// `number`, and answers `false`.

/** @requires safeInteger(e) && 0 <= e */
export function pastOrPositive(xs: number[], e: number): boolean {
  return e < xs.length || xs[e]! > 0;
}
