// A guard on a field holding an array beside null or a number, a native
// call whose callback keeps the heap, then the field's reread: `map` and
// `forEach` at a callback within the empty footprint are within it, so the
// call keeps what the guard found. Stands for the census functions
// claim-text.mts#liftClause (`t.optional.map` after `t.required.map`) and
// diagnostic.mts#readDiagnostic (`claim.context.forEach` after
// `available.forEach`).
type Value = null | number | readonly Value[];
type Row = { readonly required: Value; readonly optional: Value };
function isList(v: Value): v is readonly Value[] {
  return Array.isArray(v);
}
function size(v: Value): number {
  return typeof v === "number" ? v : 0;
}
export function sizes(t: Row): number[] {
  if (!isList(t.required) || !isList(t.optional)) return [];
  const required = t.required.map((v) => size(v));
  return t.optional.map((v) => size(v) + required.length);
}
export function count(t: Row, seen: Value): number {
  if (!Array.isArray(seen) || !Array.isArray(t.optional)) return 0;
  seen.forEach(size);
  return t.optional.length;
}
