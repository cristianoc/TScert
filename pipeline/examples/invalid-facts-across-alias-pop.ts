// A call popping an array that may be the one whose length bounded the
// index: `pop` changes its receiver's store, and no length survives it.
// Under Node, `drained(xs, xs)` with `xs = [1, 2, 3]` reads `xs[1]` of `[1]`,
// `undefined` at `number`, and answers `NaN`.

export function drained(xs: number[], ys: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    ys.pop();
    s = s + xs[i]!;
  }
  return s;
}
