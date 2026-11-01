// Undefined elements and holes at any array depth serialize as null.
export function nested(
  rows: readonly (readonly (string | undefined)[] | undefined)[],
): string {
  return JSON.stringify(rows);
}
export function keys(
  rows: readonly (string | undefined)[],
  names: string[],
): string {
  return JSON.stringify(rows, names, 2);
}
