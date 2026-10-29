// An assertion function's actual is the first of two reads of one field,
// the second after a write: the promise is about the first read's value,
// and the field holds the written one. Under Node, `size({ args: [1] })`
// reads `length` off 1, `undefined`.
function assertFirst(
  value: readonly number[] | number,
  other: readonly number[] | number,
): asserts value is readonly number[] {
  if (!Array.isArray(value)) throw new Error("not a list");
}
function reset(x: { args: readonly number[] | number }): number {
  x.args = 1;
  return 0;
}
export function size(x: { args: readonly number[] | number }): number {
  assertFirst(x.args, reset(x) + 0 === 0 ? x.args : 0);
  return x.args.length;
}
