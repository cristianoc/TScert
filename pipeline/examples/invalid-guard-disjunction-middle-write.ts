// A guard on a field in a disjunction's first operand, a call writing the
// field in the middle one: where `!isRow(x.f) || (reset(x), false) || a` is
// false, `x.f` holds 1, whose `context` is `undefined`, so `length` throws
// a TypeError: `size({ f: { context: [] } }, false)` under Node.
type Row = { readonly context: readonly number[] };
function isRow(v: Row | number): v is Row {
  return typeof v !== "number";
}
function reset(x: { f: Row | number }): void {
  x.f = 1;
}
export function size(x: { f: Row | number }, a: boolean): number {
  if (!isRow(x.f) || (reset(x), false) || a) return 0;
  return x.f.context.length;
}
