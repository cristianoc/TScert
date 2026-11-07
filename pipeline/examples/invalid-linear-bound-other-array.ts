// A bound by another array's length: `j < ys.length` bounds j by ys's store,
// not xs's, and the write leaves a hole in a shorter xs (run under Node:
// `wrongOther([5], [1,2,3])` gives `[5, <1 empty item>, 0]`, `xs[1]` undefined).
export function wrongOther(xs: number[], ys: number[]): void {
  let j = 0;
  if (ys.length > 2) {
    j = 2;
    if (j < ys.length) xs[j] = 0;
  }
}
