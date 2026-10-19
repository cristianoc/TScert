// `!isRecord(v) && n > 3` is false where the guard answered `true` or where
// `n > 3` failed: on that outcome the guard promises nothing, and `v` stays
// at its declared type, which the return refuses.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
type Fields = { [key: string]: Json };
function isRecord(v: Json | undefined): v is Fields {
  if (typeof v !== "object" || v === null || Array.isArray(v)) return false;
  return true;
}
export function wrong(v: Json | undefined, n: number): Fields {
  if (!isRecord(v) && n > 3) throw Error("invalid");
  return v;
}
