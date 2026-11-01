// A fresh snapshot mapped into a writable result, expressed as a loop.
// Census functions:
// host-families.mts#familyTable
export function arms(
  xs: number[],
  arm: (x: number) => string,
  extra: boolean,
): string[] {
  const result: string[] = [];
  for (const x of xs.slice()) result.push(arm(x));
  if (extra) result.push("extra");
  return result;
}
