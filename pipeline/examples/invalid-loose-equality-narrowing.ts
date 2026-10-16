// A successful coercive comparison does not establish the other operand's type.
function wrongNumber(value: string | number, other: number): number {
  if (value == other) return value;
  return 0;
}
