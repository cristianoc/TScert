// A decoder closing with a double assertion through unknown.
// Census functions:
// diagnostic.mts#readDiagnostic
export function decode(value: { id: unknown }): { id: string } | undefined {
  if (typeof value.id !== "string") return undefined;
  return value as unknown as { id: string };
}
