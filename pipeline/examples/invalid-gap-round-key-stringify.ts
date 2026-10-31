// A missing field key cannot meet the JSON data contract.
// Census functions:
// claim-text.mts#atomText
// claim-text.mts#bareAtomText
// claim-text.mts#typeText
// claim-text.mts#printType
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
function isObject(v: Json | undefined): v is { [key: string]: Json } {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}
export function keyText(field: { [key: string]: Json }): string {
  const key = field.name;
  return typeof key === "string"
    ? key
    : isObject(key) && typeof key.symbol === "number"
      ? `[symbol ${key.symbol}]`
      : JSON.stringify(key);
}
