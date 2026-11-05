// A literal whose discriminant names an arm its other fields do not meet is
// no element of the array.
type D = { kind: "a"; v: number } | { kind: "b"; w: string };
export function add(items: D[]): number {
  return items.push({ kind: "a", w: "x" } as unknown as D);
}
