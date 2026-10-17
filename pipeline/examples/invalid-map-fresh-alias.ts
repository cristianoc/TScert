// A constant naming the mapped array is no store the callback allocated:
// `pop` through it changes the mapped array's store, so `map` takes its
// signature with holes.
export function drained(xs: string[]): string[] {
  return xs.map((x) => {
    const a = xs;
    a.pop();
    return x;
  });
}
