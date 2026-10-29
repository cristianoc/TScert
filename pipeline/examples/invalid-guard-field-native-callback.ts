// A native call between a guard and the reread of the field it tested, whose
// callback writes the field: `forEach` is within the callback's footprint,
// which may change every location, so the reread is of a field that may hold
// a number, of which `length` is `undefined` (run under Node).
type Box = { args: readonly number[] | number };
function isList(value: readonly number[] | number): value is readonly number[] {
  return Array.isArray(value);
}
export function wrong(x: Box, seen: readonly number[]): number {
  if (!isList(x.args)) return 0;
  seen.forEach(() => {
    x.args = 0;
  });
  return x.args.length;
}
