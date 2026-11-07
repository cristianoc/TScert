// A loop reassigning its index below where it started: `i = j - 2` admits
// `i = -1`. Under Node, `runSum([1, 2])` reads `xs[-1]`, `undefined` at
// `number`, and answers `NaN`.

export function runSum(xs: number[]): number {
  const n = xs.length;
  let count = 0;
  let sum = 0;
  for (let i = 0; i < n && count < 3; ) {
    const v = xs[i]!;
    sum = sum + v;
    let j = i + 1;
    while (j < n && xs[j]! === v) j++;
    count = count + 1;
    i = j - 2;
  }
  return sum;
}
