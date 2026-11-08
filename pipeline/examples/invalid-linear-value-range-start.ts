// A loop from `i - 1` under `0 <= i` alone: `j` may start at -1, and the
// read is refused (run under Node: `sumFromBefore([1], 0)` reads `xs[-1]`,
// `undefined` at `number`).

/** @requires safeInteger(i) && 0 <= i */
export function sumFromBefore(xs: number[], i: number): number {
  let s = 0;
  for (let j = i - 1; j < xs.length; j++) s += xs[j]!;
  return s;
}
