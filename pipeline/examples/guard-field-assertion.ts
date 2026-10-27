// An assertion function on a field: where it returns, the field reread holds
// the asserted type, its body keeping the heap.
function assertList(
  value: readonly number[] | number,
): asserts value is readonly number[] {
  if (!Array.isArray(value)) throw new Error("not a list");
}
export function size(x: { args: readonly number[] | number }): number {
  assertList(x.args);
  return x.args.length;
}
