// The twin of invalid-guard-disjunction-after-test-write, of the same
// spans: its `reset` reads the field and writes nothing, so where the
// disjunction is false, `x.f` is still the guarded `Row`; the control
// gives its claims to the negative, whose `reset` writes the number 1 to the field.
type Row = { readonly context: readonly number[] };
function isRow(v: Row | number): v is Row {
  return typeof v !== "number";
}
function reset(x: { f: Row | number }): void {
  x.f;    
}
export function size(x: { f: Row | number }, other: string): number {
  if (other !== "k" || !isRow(x.f) || (reset(x), false)) return 0;
  return x.f.context.length;
}
