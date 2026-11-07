// A loop whose index is reassigned from one derived from it: `j` starts at
// `i + 1` and only grows, so `i = j` keeps `0 <= i`. Reassigning a binding,
// or leaving its scope, eliminates it from the linear facts (Fourier–Motzkin),
// keeping what they state of the others: `1 <= j` from `j = i + 1` and
// `0 <= i`.

export function runCount(xs: number[]): number {
  const n = xs.length;
  let count = 0;
  for (let i = 0; i < n; ) {
    const v = xs[i]!;
    let j = i + 1;
    while (j < n && xs[j]! === v) j++;
    count = count + 1;
    i = j;
  }
  return count;
}
