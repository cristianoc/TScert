// Awaiting a promise of a number, or a string, yields either: not a number.
export async function mixed(
  b: boolean,
  p: Promise<number>,
  s: string,
): Promise<number> {
  const x = b ? p : s;
  return await x;
}
