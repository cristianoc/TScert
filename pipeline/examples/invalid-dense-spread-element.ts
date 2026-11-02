export function wrong(
  target: number[],
  values: (number | undefined)[],
  next: () => number,
): void {
  // @ts-expect-error: an undefined actual does not meet a numeric rest.
  target.push(...values, next());
}
