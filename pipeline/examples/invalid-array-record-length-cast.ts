// A union of an array and a record with its own `length`, a string: the
// record's member is no array contract, and its `length` is its own field's.
// The read is of `number | string`, and the cast to `number` is refused (run
// under Node: `size({ length: "two" })` passes the test with a string).
export function size(
  x: readonly number[] | { readonly length: string },
): number {
  if ((x.length as number) !== 0) return 1;
  return 0;
}
