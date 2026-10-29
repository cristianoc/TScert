// An assertion function on a field, then a call writing the field, then the
// field's reread: the call keeps no heap fact, so the reread is at the
// field's contract. TypeScript keeps the narrowing past the call: under
// Node, `size({ args: [1] })` reads `length` off 1, `undefined`.
function assertList(
  value: readonly number[] | number,
): asserts value is readonly number[] {
  if (!Array.isArray(value)) throw new Error("not a list");
}
function reset(x: { args: readonly number[] | number }): void {
  x.args = 1;
}
export function size(x: { args: readonly number[] | number }): number {
  assertList(x.args);
  reset(x);
  return x.args.length;
}
