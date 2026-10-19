// `Object.fromEntries` of an array of string-keyed pairs: the host's array
// iterator and data pairs, a fresh dictionary of the values, within the
// empty footprint.
export function table(pairs: readonly (readonly [string, number])[]): {
  [k: string]: number;
} {
  return Object.fromEntries(pairs);
}
export function tables(
  rows: (readonly (readonly [string, number])[])[],
): { [k: string]: number }[] {
  return rows.map((r) => Object.fromEntries(r));
}
