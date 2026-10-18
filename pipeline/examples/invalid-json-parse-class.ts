// A class instance is no parsed JSON: its prototype holds members a read
// by key finds, and a record type that admits it states none of them, so it
// is refused where `ParsedJson` is required.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
class Point {
  x: number;
  constructor(x: number) {
    this.x = x;
  }
  describe(): string {
    return "point";
  }
}
type XY = { x: number };
function described(v: Json): Json {
  if (v === null || typeof v !== "object" || Array.isArray(v)) return null;
  return v["describe"] ?? null;
}
export function wrong(): Json {
  const p: XY = new Point(1);
  return described(p);
}
