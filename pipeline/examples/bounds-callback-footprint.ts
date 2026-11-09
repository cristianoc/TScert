// Pretext line-break's visitor: a stated callback footprint keeps array bounds.
export function visit(
  xs: number[],
  callback: (n: number) => Modifies<{ values: "any" }, void>,
): number {
  let total = 0;
  for (let i = 0; i < xs.length; i++) {
    callback(i);
    total += xs[i]!;
  }
  return total;
}
export function caller(xs: number[]): number {
  let count = 0;
  return visit(xs, (i: number): void => {
    count += i;
  });
}
