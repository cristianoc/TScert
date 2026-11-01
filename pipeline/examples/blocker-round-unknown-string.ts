// String conversion after explicit primitive tests of a JSON value.
// Census functions:
// claim-text.mts#atomText
// claim-text.mts#bareAtomText
// claim-text.mts#typeText
// claim-text.mts#printType
// claim-text.mts#liftClause
// claim-text.mts#liftSignatures
// claim-text.mts#liftType
// claim-text.mts#liftLabels
// claim-text.mts#treeAtom
// claim-text.mts#lift
type JsonValue =
  | null
  | boolean
  | number
  | string
  | readonly JsonValue[]
  | { readonly [key: string]: JsonValue };
function isObject(
  value: JsonValue,
): value is { readonly [key: string]: JsonValue } {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
export function print(value: JsonValue): string {
  if (Array.isArray(value)) return "«type»";
  if (!isObject(value)) {
    if (
      typeof value === "string" ||
      typeof value === "number" ||
      typeof value === "boolean" ||
      value === null
    )
      return String(value);
    return "«type»";
  }
  return "«type»";
}
