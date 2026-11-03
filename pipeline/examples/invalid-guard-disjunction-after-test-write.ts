// A test, then a guard on a field, then a disjunct calling a function that
// writes the field: where `other !== "k" || !isRow(x.f) || (reset(x), false)`
// is false, `x.f` holds 1, whose `context` is `undefined`, so `length`
// throws a TypeError: `size({ f: { context: [] } }, "k")` under Node.
type Row = { readonly context: readonly number[] };
function isRow(v: Row | number): v is Row {
  return typeof v !== "number";
}
function reset(x: { f: Row | number }): void {
  x.f = 1;
}
export function size(x: { f: Row | number }, other: string): number {
  if (other !== "k" || !isRow(x.f) || (reset(x), false)) return 0;
  return x.f.context.length;
}
