// A decoder of a parsed list closing with an assertion its checks do not
// establish: `some` answers a Boolean and leaves the list at its JSON type, and
// the assertion promises a writable list of numbers on the parsed list's own
// storage (`decodeLabels` and `decodeGraph` of `tools/type-graph.mts`,
// `decodeClaimType` and `atom` of `tools/claim.mts`). The caller keeps the
// parsed list at its JSON type and writes a string into it after the decoder
// returns, which the decoded list then holds (run under Node: `typeof
// first('[1]')` is "string").
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
type JsonValue =
  | null
  | boolean
  | number
  | string
  | readonly JsonValue[]
  | { readonly [key: string]: JsonValue };
const isList = (v: JsonValue | undefined): v is readonly JsonValue[] =>
  Array.isArray(v);
export function decode(v: JsonValue | undefined, size: number): number[] {
  if (!isList(v)) throw Error("expected a list");
  if (v.some((i) => typeof i !== "number" || i < 0 || i >= size))
    throw Error("reference out of bounds");
  return v as number[];
}
export function first(text: string): number | undefined {
  const parsed: Json = JSON.parse(text);
  const labels = decode(parsed, 2);
  if (Array.isArray(parsed)) parsed[0] = "x";
  return labels[0];
}
