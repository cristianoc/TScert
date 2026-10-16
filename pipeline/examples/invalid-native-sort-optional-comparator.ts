// A possibly absent comparator does not justify sorting arbitrary objects.
export function wrong(
  xs: { key: number }[],
  compare: ((a: { key: number }, b: { key: number }) => number) | undefined,
): { key: number }[] {
  return xs.sort(compare);
}
