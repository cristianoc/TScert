// The shape of shadow-contracts.mts#print's `all` (line 122): the parts a map
// gives, tested by a guard excluding null, then mapped at string and joined.
// Census functions: shadow-contracts.mts#print, shadow-contracts.mts#prelude.
function show(x: number): string | null {
  return x > 0 ? `${x}` : null;
}

export function all(
  terms: readonly number[],
  separator: string,
): string | null {
  const parts = terms.map(show);
  return parts.every((part): part is string => part !== null)
    ? parts.map((p) => `(${p})`).join(separator)
    : null;
}
