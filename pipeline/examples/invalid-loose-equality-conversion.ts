// An open record may convert through a user-defined hook with effects.
function objectConversion(
  value: { tag: number } | number,
  other: number,
): boolean {
  return value == other;
}
