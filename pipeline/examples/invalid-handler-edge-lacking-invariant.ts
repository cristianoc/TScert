// A loop invariant at the entry of a catch block, on a local the try block
// sets from an argument before a call that throws: the handler's edge does
// not establish `0 <= i`. Under Node `h([1], -1)` reads `xs[-1]` and returns
// `NaN` where every element read is claimed a number. The refusal names the
// invariant's facts the handler's edge lacks.
function boom(n: number): number {
  if (n < 0) throw new Error("negative");
  return n;
}
export function h(xs: number[], j: number): number {
  let s = 0;
  let i = 0;
  try {
    i = j;
    s = boom(j);
  } catch {
    /** @invariant safeInteger(i) && 0 <= i */
    while (i < xs.length) {
      s += xs[i]!;
      i++;
    }
  }
  return s;
}
