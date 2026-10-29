// An assertion function's call whose later actual writes the field its
// first actual read: the promise is about the value read, and the field
// holds the written number. Under Node, `size({ args: [1] })` reads
// `length` off 1, `undefined`.
function assertFirst(
  value: readonly number[] | number,
  other: number,
): asserts value is readonly number[] {
  if (!Array.isArray(value)) throw new Error("not a list");
}
function reset(x: { args: readonly number[] | number }): number {
  x.args = 1;
  return 0;
}
export function size(x: { args: readonly number[] | number }): number {
  assertFirst(x.args, reset(x));
  return x.args.length;
}
