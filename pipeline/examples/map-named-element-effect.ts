// Census functions: named-record.mts#kindsText and its text callers.
// A named element contract excludes undefined, giving map its dense receiver
// and its callback's empty footprint.
type Kind = "string" | "number";
type Kinds = readonly Kind[];

export function kindsText(
  kinds: Kinds | null,
): Within<{ value: "keep"; store: "keep" }, string> {
  return kinds === null
    ? "null"
    : `[${kinds.map((k) => JSON.stringify(k)).join(",")}]`;
}
