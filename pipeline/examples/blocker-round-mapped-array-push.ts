// A mapped array used as a push receiver.
// Census functions:
// host-families.mts#familyTable
export function arms(
  xs: number[],
  arm: (x: number) => string,
  extra: boolean,
): string[] {
  const result = xs.map((x) => arm(x));
  if (extra) result.push("extra");
  return result;
}
