// A call between a guard keeping the heap and the reread of the field it
// tested may write the field: the reread is of a field that may hold a number,
// of which `length` is `undefined` (run under Node).
type Box = { args: readonly number[] | number };
function isList(value: readonly number[] | number): value is readonly number[] {
  return Array.isArray(value);
}
export function wrong(x: Box, reset: () => void): number {
  if (isList(x.args)) {
    reset();
    return x.args.length;
  }
  return 0;
}
