// A recovered condition retains distinct identities for its synthetic expressions.
export function syntaxBranch(value: unknown): boolean {
  if (value instanceof Uint8Array) return true;
  return false;
}
