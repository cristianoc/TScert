// A parsed object inherits `Object.prototype`: a read at a key it provides,
// `toString`, finds a function, which no `ParsedJson` is.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
export function wrong(text: string): Json {
  const v: Json = JSON.parse(text);
  if (v === null || typeof v !== "object" || Array.isArray(v)) return null;
  return v["toString"] ?? null;
}
