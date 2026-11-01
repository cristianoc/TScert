// A callback can shrink the shared receiver and leave a hole in map's result.
export function arms(
  xs: number[],
  arm: (x: number) => string,
  extra: boolean,
): string[] {
  const result = xs.map((x) => arm(x));
  if (extra) result.push("extra");
  return result;
}
