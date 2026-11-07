// A counter from 0, below the array's length: each write lands at an index
// at most the length, with no guard; the counter's facts at the loop head
// (a safe integer, at least 0, at most 2^32 - 1) are kept by the increment.
export function clear(xs: number[]): void {
  for (let j = 0; j < xs.length; j++) {
    xs[j] = 0;
  }
}

export function fill(xs: (string | null)[], v: string): void {
  let j = 0;
  while (j < xs.length) {
    xs[j] = v;
    j = j + 1;
  }
}
