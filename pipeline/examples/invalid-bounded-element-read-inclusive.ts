// The loop runs to `j <= xs.length`: its last read is past the end, `undefined`
// at `number` (run under Node: `sum([1, 2])` is `NaN`).
export function sum(xs: number[]): number {
  let s = 0;
  for (let j = 0; j <= xs.length; j++) s = s + xs[j]!;
  return s;
}
