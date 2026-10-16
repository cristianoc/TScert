// The alias's tuple is `[number, string]`: its first position is no string.
type Pair<A, B> = readonly [A, B];
export function pairLayout(
  f: (...args: Pair<number, string>) => string,
): (a: string, b: string) => string {
  return f;
}
