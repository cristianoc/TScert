// A declared guard states no effect, so the call may write the field it tests:
// the reread is of a field that may hold a number.
declare function isList(
  value: readonly number[] | number,
): value is readonly number[];
export function size(x: { args: readonly number[] | number }): number {
  if (isList(x.args)) return x.args.length;
  return 0;
}
