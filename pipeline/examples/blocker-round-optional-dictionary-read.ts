// Optional bound lookup through the native Map contract.
// Census functions:
// array-prototype.mts#primitivePrototype
// array-prototype.mts#functionPrototype
// array-prototype.mts#prototype
export function bound(
  bounds: Map<string, string> | undefined,
  name: string,
): string | null {
  return bounds?.get(name) ?? null;
}
