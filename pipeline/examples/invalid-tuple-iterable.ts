// A tuple of numbers iterates numbers, not strings.
export function wrong(): void {
  const t: [number, number] = [1, 2];
  // @ts-expect-error A number is no string.
  const it: Iterable<string> = t;
  void it;
}
