export function back<T extends number | Promise<number>>(value: Awaited<T>): T {
  return value;
}
