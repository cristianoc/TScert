// A constant one branch gives a fresh array and the other the mapped one:
// the store is fresh on one incoming edge only, so `pop` through it is
// bounded by its signature without the exception, and the result has holes.
export function drained(xs: string[]): string[] {
  return xs.map((x) => {
    const a = x.length > 1 ? x.split("") : xs;
    a.pop();
    return x;
  });
}
