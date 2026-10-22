// Another name for the same array shrinks it between the length's read and
// the element's: the index is past the end, and the read is `undefined`.
export function aliased(xs: string[], ys: string[]): string {
  const n = xs.length;
  ys.pop();
  return xs[n - 1];
}
