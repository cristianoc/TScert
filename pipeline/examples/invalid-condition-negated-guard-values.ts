type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
type Fields = { [key: string]: Json };
function isRecord(v: Json | undefined): v is Fields {
  if (typeof v !== "object" || v === null || Array.isArray(v)) return false;
  return true;
}
// `!isRecord(v) && n` is false where the guard answered `false` and `n` is
// 0: there `v` may be `null`, and its cast is refused (`wrong(null, 0)`
// throws under Node).
export function wrong(v: Json | undefined, n: number): string[] {
  if (!isRecord(v) && n) throw Error("invalid");
  return Object.keys(v as Fields);
}
