// A guard writing the field it tests through another reference: its answer
// is of the value it was passed, and the reread gives the value it wrote, of
// which `length` is `undefined` (run under Node).
type Box = { args: readonly number[] | number };
function isListAfter(
  value: readonly number[] | number,
  alias: Box,
): value is readonly number[] {
  alias.args = 0;
  return Array.isArray(value);
}
export function wrong(x: Box): number {
  if (isListAfter(x.args, x)) return x.args.length;
  return 0;
}
