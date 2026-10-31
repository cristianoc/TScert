// An optional dictionary read at a key that can name an inherited member.
// Census functions:
// array-prototype.mts#primitivePrototype
// array-prototype.mts#functionPrototype
// array-prototype.mts#prototype
export function bound(
  bounds: Readonly<Record<string, string>> | undefined,
  name: string,
): string | null {
  return bounds?.[name] ?? null;
}
