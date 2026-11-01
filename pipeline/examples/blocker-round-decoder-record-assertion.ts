// A decoder allocates a result with its checked writable field contract.
// Census functions:
// diagnostic.mts#readDiagnostic
export function decode(value: { id: unknown }): { id: string } | undefined {
  const parsed: { id: unknown } = { id: value.id };
  const id = parsed.id;
  if (typeof id !== "string") return undefined;
  return { id };
}
