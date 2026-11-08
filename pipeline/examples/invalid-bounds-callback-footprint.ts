// A callback violating the walker's footprint removes the element to be read.
function visit(xs: number[], callback: () => Within<{value: "any"; store: "keep"}, void>): number {
  if (xs.length === 0) return 0;
  callback();
  return xs[0]!;
}
export function broken(xs: number[]): number {
  return visit(xs, (): void => { xs.pop(); });
}
