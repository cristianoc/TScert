// A manifest read from `JSON.parse` keeps its JSON type: a member is read
// after the tests that leave the dictionary arm, and a member's text is
// computed by the arms, as `String` converts it (`tools/files.mts`,
// `tools/family-activation.mts`).
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export function member(
  manifest: Json,
  key: "name" | "version",
): Json | undefined {
  if (
    typeof manifest !== "object" ||
    manifest === null ||
    Array.isArray(manifest)
  )
    return undefined;
  return manifest[key];
}
export function text(value: Json): string {
  if (typeof value !== "object" || value === null) return String(value);
  if (Array.isArray(value))
    return value.map((x: Json) => (x === null ? "" : text(x))).join(",");
  if (Object.hasOwn(value, "toString"))
    throw new TypeError("Cannot convert object to primitive value");
  return "[object Object]";
}
export function version(source: string): string {
  const manifest: Json = JSON.parse(source);
  const found = member(manifest, "version");
  return found === undefined ? "" : text(found);
}
export function named(source: string, name: string): boolean {
  const manifest: Json = JSON.parse(source);
  return member(manifest, "name") === name;
}
