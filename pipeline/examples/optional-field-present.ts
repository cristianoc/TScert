// A required field covers an optional one of the same key and contract.
function read(value: { field?: number }): number | undefined {
  return value.field;
}
export function pass(value: { field: number }): number | undefined {
  return read(value);
}
