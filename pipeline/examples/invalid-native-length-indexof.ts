export function absent(xs: string[], value: string): string {
  const at = xs.indexOf(value);
  return xs[at]!.toUpperCase();
}
