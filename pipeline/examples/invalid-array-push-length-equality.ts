// A push keeps only lower bounds of its receiver's length: after `xs.push(0)`
// the equality `xs.length === ys.length` no longer holds, and the read of
// `ys` at `xs.length - 1` is refused (run under Node: `lastOf([1], [2])`
// reads `ys[1]`, `undefined` at `number`).

/** @requires xs.length === ys.length */
export function lastOf(xs: number[], ys: number[]): number {
  xs.push(0);
  if (xs.length === 0) return 0;
  return ys[xs.length - 1]!;
}
