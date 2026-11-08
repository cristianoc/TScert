// A prefix update inside an index reads at the new value: `xs[++at]!` with
// `at < xs.length` reads one past the old bound, and the read is refused (run
// under Node: `nextOf([1], 0)` reads `xs[1]`, `undefined` at `number`).

/** @requires safeInteger(at) && 0 <= at && at < xs.length */
export function nextOf(xs: number[], at: number): number {
  return xs[++at]!;
}
