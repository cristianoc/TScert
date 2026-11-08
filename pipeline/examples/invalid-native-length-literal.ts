export function past(a: string): string {
  const xs: string[] = [a, a];
  return xs[2]!.toUpperCase();
}
