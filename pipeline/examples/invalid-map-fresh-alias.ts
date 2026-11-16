// A constant naming the mapped array is no spine the callback allocated:
// `pop` through it changes the mapped array's spine, so `map` takes its
// signature with holes.
export function drained(xs: string[]): string[] {
  return xs.map((x) => {
    const a = xs;
    a.pop();
    return x;
  });
}
