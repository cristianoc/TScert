// A conditional spread of a record literal holding a tuple field, expected at
// a discriminated union: the spread's literal is built at the fields the arms
// give, its tuple at the tuple type.
// Census functions:
// fragment-classes.mts#classBody, fragment-classes.mts#classStmt.
type Span = [start: number, end: number];
type E =
  | { k: "id"; pos: Span; name: string }
  | { k: "alloc"; pos: Span; fields: { name: string; e: E }[]; proto?: E; brand?: { key: string; pos: Span } };
type B = { name: string; init: E | null };
export function bound(out: B[], fields: { name: string; e: E }[], baseProto: E | null, tested: boolean, key: string): void {
  const at: Span = [0, 1];
  out.push({ name: "x", init: { k: "alloc", pos: at, fields, ...(baseProto ? { proto: baseProto } : {}),
    ...(tested ? { brand: { key, pos: [2, 3] } } : {}) } });
}
export function returned(fields: { name: string; e: E }[], tested: boolean, key: string): E {
  return { k: "alloc", pos: [0, 1], fields, ...(tested ? { brand: { key, pos: [2, 3] } } : {}) };
}
