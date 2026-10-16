// A closure collecting a rest runs its loop as graph code: with no further
// actuals nothing is found, and the null the local starts with is returned.
export function last(seed: number): number {
  const pick = (first: number, ...rest: number[]): number => {
    let found: number | null = null;
    for (const x of rest) {
      found = x + first;
    }
    return found as number;
  };
  return pick(seed);
}
