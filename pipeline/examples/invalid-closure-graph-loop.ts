// A loop in a closure: over an empty array nothing is found, and the null the
// local starts with is returned.
export function last(xs: number[]): () => number {
  return (): number => {
    let found: number | null = null;
    for (const x of xs) {
      found = x;
    }
    return found as number;
  };
}
