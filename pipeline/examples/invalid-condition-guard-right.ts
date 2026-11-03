type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
type Fields = { [key: string]: Json };
function isRecord(v: Json | undefined): v is Fields {
  if (typeof v !== "object" || v === null || Array.isArray(v)) return false;
  return true;
}
// `n > 3 && !isRecord(v)` is false where `n` is at most 3, whatever `v` is:
// its cast is refused (`wrong(null, 0)` throws under Node).
export function wrong(v: Json | undefined, n: number): string[] {
  if (n > 3 && !isRecord(v)) throw Error("invalid");
  return Object.keys(v as Fields);
}
