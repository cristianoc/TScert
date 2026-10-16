// Arrays cannot own conversion methods, even an apparently harmless one.
// The normal method is inherited; this intersection requires an own field.
export function override(
  value: [number, number] & { toString: () => string },
): string {
  return value.toString();
}
