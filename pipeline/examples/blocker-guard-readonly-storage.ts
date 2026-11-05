// Testing readonly dictionary contents does not establish writable field
// contracts (SOURCE-MODEL, writable string index signatures).
// Census functions:
// type-graph.mts#decodeCallEffect, type-graph.mts#decodeClosedFootprint.
type Dict = { readonly [key: string]: string };
export function use(value: Dict): value is { value: "keep" | "any" } {
  return value.value === "keep" || value.value === "any";
}
