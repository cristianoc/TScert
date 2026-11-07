// A read at an index the loop's condition bounds, `i < xs.length`, is at the
// element type: nothing between the test and the read writes the array.
// TypeScript under `noUncheckedIndexedAccess` types the read `string |
// undefined` and refuses `xs[i].length`.
export function total(xs: string[]): number {
  let n = 0;
  for (let i = 0; i < xs.length; i++) n += xs[i].length;
  return n;
}
