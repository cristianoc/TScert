// A growing callback changes the receiver length after map captures it.
export function changed(xs: string[]): string {
  const ys = xs.map((x) => {
    xs.push("extra");
    return x;
  });
  return xs.length > 0 ? ys[xs.length - 1]!.toUpperCase() : "";
}
