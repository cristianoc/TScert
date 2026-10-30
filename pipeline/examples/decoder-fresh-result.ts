// A decoder of parsed JSON returns fresh storage built from the values it
// checked: a list of in-bounds numbers, each element tested as `map` visits
// it, and a record of a Boolean and such a list, each field tested where it
// is read (`decodeLabels` and `decodeGraph` of `tools/type-graph.mts`,
// `decodeClaimType` and `atom` of `tools/claim.mts`). A later write to the
// parsed value leaves the decoded one as it was.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
type JsonValue =
  | null
  | boolean
  | number
  | string
  | readonly JsonValue[]
  | { readonly [key: string]: JsonValue };
type JsonObject = { readonly [key: string]: JsonValue };
type Decoded = { top: boolean; labels: number[] };
const isList = (v: JsonValue | undefined): v is readonly JsonValue[] =>
  Array.isArray(v);
const isRecord = (v: JsonValue | undefined): v is JsonObject =>
  typeof v === "object" && v !== null && !Array.isArray(v);
export function decode(v: JsonValue | undefined, size: number): number[] {
  if (!isList(v)) throw Error("expected a list");
  return v.map((i) => {
    if (typeof i !== "number" || i < 0 || i >= size)
      throw Error("reference out of bounds");
    return i;
  });
}
export function decodeRecord(v: JsonValue | undefined, size: number): Decoded {
  if (!isRecord(v) || Object.keys(v).length !== 2)
    throw Error("expected a record");
  const top = v.top;
  if (typeof top !== "boolean") throw Error("expected a boolean");
  return { top, labels: decode(v.labels, size) };
}
export function first(text: string): number | undefined {
  const parsed: Json = JSON.parse(text);
  const labels = decode(parsed, 2);
  if (Array.isArray(parsed)) parsed[0] = "x";
  return labels[0];
}
export function flag(text: string): boolean {
  const parsed: Json = JSON.parse(text);
  const decoded = decodeRecord(parsed, 2);
  decoded.labels.push(1);
  return decoded.top;
}
