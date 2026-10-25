// A loop bound needs to establish that an array read is in bounds.
// Model study: 5 Sonnet samples (bounded-index-read.ts).
export function pairwiseDiff(xs: number[]): number[] {
  const result: number[] = [];
  for (let i = 1; i < xs.length; i++) {
    result.push(xs[i]! - xs[i - 1]!);
  }
  return result;
}
