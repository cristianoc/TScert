// A dictionary's read at a numeric key typed as a union of `number` with a
// literal, or of literals alone: every value the key holds is a number,
// which names an entry, exactly as a `number` key's read — one meaning, one
// decision.
export function lookup(
  table: { [key: number]: string },
  key: number | 0,
): string | undefined {
  return table[key];
}

export function lookupLiteral(
  table: { [key: number]: string },
  key: 0 | 1,
): string | undefined {
  return table[key];
}
