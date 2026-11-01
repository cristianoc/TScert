// A field test cannot change a writable alias's storage contract.
export function decode(value: { id: unknown }): { id: string } | undefined {
  if (typeof value.id !== "string") return undefined;
  return value as unknown as { id: string };
}
