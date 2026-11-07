// A read at `i + 1` under the loop test `i < xs.length`: its last iteration
// reads at the length. Under Node, `pairProducts([1, 2])` reads `xs[2]`,
// `undefined` at `number`, and answers `NaN`.

export function pairProducts(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) s = s + xs[i]! * xs[i + 1]!;
  return s;
}
