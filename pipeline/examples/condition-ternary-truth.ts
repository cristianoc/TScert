export function use(
  x: string | undefined,
  take: (s: string) => string,
): string {
  return !x || false ? "" : take(x);
}
