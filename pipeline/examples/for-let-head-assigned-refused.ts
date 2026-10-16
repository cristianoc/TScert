// A `let` in a `for...of` head the body assigns is a cell per iteration,
// which the loop's lowering does not bind.
export function sum(xs: number[]): number {
  let s = 0;
  for (let x of xs) {
    x = x + 1;
    s = s + x;
  }
  return s;
}
