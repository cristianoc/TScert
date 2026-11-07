// A test of two lengths the facts already state equal, `xs.length !==
// ys.length` under the precondition `xs.length === ys.length`, is refused at
// the edge from the test's second evaluation into its branch (the cause is
// not established). The program is safe: the test is `false` and the throw
// unreachable. A builder testing a view's element count after allocating it
// at `widths.length` (`new Uint8Array(widths.length)`, which states it) meets
// the same refusal.

/** @requires xs.length === ys.length */
export function f(xs: number[], ys: number[]): number {
  if (xs.length !== ys.length) throw new RangeError("lengths differ");
  return xs.length;
}
