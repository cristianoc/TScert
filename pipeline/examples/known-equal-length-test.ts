// A test of two lengths the facts already state equal, `xs.length !==
// ys.length` under the precondition `xs.length === ys.length`: its `false`
// answer's `≠` and the precondition's equality are a contradiction once both
// length reads are dropped, a fact naming no variable, which the entailment
// search reads over every held fact (`Linear.relevant`). The test is `false`
// and the throw unreachable.

/** @requires xs.length === ys.length */
export function f(xs: number[], ys: number[]): number {
  if (xs.length !== ys.length) throw new RangeError("lengths differ");
  return xs.length;
}
