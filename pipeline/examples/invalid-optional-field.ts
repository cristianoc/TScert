// An optional field may be absent: its read is not a number.
function wrong(value: { field?: number }): number {
  return value.field;
}
