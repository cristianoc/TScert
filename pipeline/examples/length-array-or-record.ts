// `length` of a union of arrays and records naming it: `Array.isArray`
// selects an array's length, its store's, and a record's field; a string's
// own length is read before either. A record owning `length` is no array.
type Named = { name: string; length: number };
export function size(x: number[] | Named): number {
  return x.length;
}
export function sizes(
  x: readonly string[] | Named,
  y: string | boolean[] | Named,
): number {
  const f = (z: number[] | Named): number => z.length;
  return x.length + y.length + f([1]) + f({ name: "n", length: 2 });
}
