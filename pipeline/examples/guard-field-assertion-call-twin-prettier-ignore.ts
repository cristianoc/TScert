// The twin of invalid-guard-field-assertion-call, of the same spans:
// `reset` reads the field and writes nothing, so the call keeps the heap
// and the reread after the assertion is at the asserted type; the control
// gives its claims to the negative, whose `reset` writes the field.
function assertList(
  value: readonly number[] | number,
): asserts value is readonly number[] {
  if (!Array.isArray(value)) throw new Error("not a list");
}
function reset(x: { args: readonly number[] | number }): void {
  x.args;    
}
export function size(x: { args: readonly number[] | number }): number {
  assertList(x.args);
  reset(x);
  return x.args.length;
}
