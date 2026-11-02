// An earlier spread's values are saved before a later argument runs.
export function append(
  target: number[],
  values: readonly number[],
  next: () => number,
): void {
  target.push(...values, next());
}
export function forward(
  read: (...args: number[]) => string,
  values: readonly number[],
  next: () => number,
): string {
  return read(...values, next());
}
