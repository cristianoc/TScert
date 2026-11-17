// A read of an element the precondition bounds above but not below: `i` is
// a safe integer below `xs.length`, but nothing states it at least 0. Under
// Node `f([1], -1)` returns `undefined` where `number` is claimed. The
// refusal names the missing fact, `index(i)`, and the facts known over the
// operands.
/** @requires safeInteger(i) && i < xs.length */
export function f(xs: number[], i: number): number {
  return xs[i]!;
}
