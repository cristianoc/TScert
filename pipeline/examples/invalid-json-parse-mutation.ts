// Parsed data stays writable at its own contract: between the enumeration
// of its keys and the read, a write through an alias of a wider element type
// stores a function, which the read then finds where parsed data is promised
// (run under Node: `typeof wrong('{"a": 1}')` is "function").
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export function wrong(text: string): Json {
  const v: Json = JSON.parse(text);
  if (v === null || typeof v !== "object" || Array.isArray(v)) return null;
  const entries = Object.entries(v);
  const alias: { [key: string]: unknown } = v;
  alias.a = () => 0;
  return entries.length > 0 ? (v.a ?? null) : null;
}
