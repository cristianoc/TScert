// A read of an element the precondition does not bound: `i` is a safe
// integer at least 0, but nothing states it below `xs.length`. Under Node
// `f([], 0)` returns `undefined` where `number` is claimed. The refusal names
// the missing fact, `i < xs.length`, and the facts known over the operands.
/** @requires safeInteger(i) && 0 <= i */
export function f(xs: number[], i: number): number {
  return xs[i]!;
}
