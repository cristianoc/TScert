// A formatting callback states the nullable element contract after every.
// Census functions:
// shadow-contracts.mts#print
// shadow-contracts.mts#printSignature
// shadow-contracts.mts#statedSignatures
// shadow-contracts.mts#prelude
// shadow-contracts.mts#shadowText
export function print(params: (string | null)[]): string[] | null {
  if (!params.every((p): p is string => p !== null)) return null;
  return params.map((p: string | null, i) => `p${i}: ${p}`);
}
