// A literal index past what the clause bounds: `1 <= xs.length` admits
// `[5]`, so `secondOf([5])` reads `xs[1]`, `undefined`, as a `number` (run
// under Node: `undefined`).

/** @requires 1 <= xs.length */
function second(xs: number[]): number {
  return xs[1]!;
}

export function secondOf(xs: number[]): number {
  if (xs.length >= 1) return second(xs);
  return 0;
}
