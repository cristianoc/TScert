// A type assertion returns its operand unchanged: the number saved before the
// field is written `null` is what is returned, not a later read of the field.
export function assertedSnapshot(x: { value: number | null }): number {
  if (x.value === null) return 0;
  const value = x.value as number;
  x.value = null;
  return value;
}
