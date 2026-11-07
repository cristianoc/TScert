// Element reads at an index the program has tested below the array's length:
// the test states the bound, which holds through statements writing no heap,
// and the read is `%ElementAt%`'s at an index below the length, the element of
// a readable `number[]`.
export function sum(xs: number[]): number {
  let s = 0;
  for (let j = 0; j < xs.length; j++) s = s + xs[j]!;
  return s;
}

export function firstPositive(xs: number[]): number {
  let i = 0;
  while (i < xs.length) {
    const x = xs[i]!;
    if (x > 0) return x;
    i = i + 1;
  }
  return 0;
}
