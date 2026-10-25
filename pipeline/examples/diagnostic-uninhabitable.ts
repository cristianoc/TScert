// Diagnostic recovery cannot supply a value at an empty destination contract.
export function impossible(value: unknown): never {
  const result: never = value;
  return result;
}
