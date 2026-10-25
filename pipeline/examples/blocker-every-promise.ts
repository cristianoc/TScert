// The every guard overload needs to carry its element promise to later
// callbacks.
// Census functions:
// shadow-contracts.mts#prelude, shadow-contracts.mts#print,
// shadow-contracts.mts#printSignature, shadow-contracts.mts#statedSignatures.
export function use(parts: (string | null)[]): string[] | null {
  return parts.every((p): p is string => p !== null)
    ? parts.map((p) => `(${p})`)
    : null;
}
