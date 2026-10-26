// A key test `"name" in m` on a value already known to be a non-null
// object, as a manifest is read from JSON.
// Census functions: family-activation.mts#selectionGuard,
// family-activation.mts#checkInventory, fragment-parse.mts#lowerFile.
export function nameOf(manifest: unknown): unknown {
  return typeof manifest === "object" && manifest !== null && "name" in manifest ? manifest.name : null;
}
