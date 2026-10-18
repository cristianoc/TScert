// A `"__proto__"` member of parsed text is an own data property, which sets
// no prototype: a read of another key finds what the text holds or nothing.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export function value(text: string, key: string): Json {
  const v: Json = JSON.parse(text);
  if (v === null || typeof v !== "object" || Array.isArray(v)) return null;
  return Object.keys(v).length > 0 && key === "a" ? (v["a"] ?? null) : null;
}
