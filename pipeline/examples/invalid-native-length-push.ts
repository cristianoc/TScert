// One push adds exactly one element: the next position is absent.
export function past(xs: string[]): string {
  const n = xs.length;
  xs.push("a");
  return xs[n + 1]!.toUpperCase();
}
