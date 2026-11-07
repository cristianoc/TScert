// A test calling a function that pops the array: the bound `i < xs.length`
// does not survive it. Under Node, `total([1, 2, 3])` reads `xs[1]` of `[1]`,
// `undefined` at `number`, and answers `NaN`.

function shrink(xs: number[]): boolean {
  xs.pop();
  return true;
}

export function total(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    if (shrink(xs)) s = s + 1;
    s = s + xs[i]!;
  }
  return s;
}
