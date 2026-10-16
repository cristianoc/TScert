// Sort has two call contracts: a checked comparator, or standard conversion of primitives and arrays.
export function byKey(xs: { key: number }[]): { key: number }[] {
  return xs.sort(
    (a: { key: number }, b: { key: number }): number => a.key - b.key,
  );
}
export function tuples(xs: [number, number][]): [number, number][] {
  return xs.sort(
    (a: [number, number], b: [number, number]): number => a[0] - b[0],
  );
}
export function explicitDefault(xs: number[]): number[] {
  return xs.sort(undefined);
}
export function noCoercion(seen: { value: number }): number {
  const entry = {
    toString: (x: number): string => {
      seen.value = x;
      return "x";
    },
  };
  const xs = [entry, entry];
  xs.sort((): number => 0);
  return seen.value;
}
