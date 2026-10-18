// A test of a field's value is a fact of the field until a write that may
// alias it or a call: a later read of the field is of the test's slice of
// the field's type. `Array.isArray` slices an array from a union with a
// string, and from `unknown` the built-ins' array.
type Mapping = { mapping: number[] | string };
export function size(t: Mapping): number {
  if (!Array.isArray(t.mapping)) return t.mapping.length;
  return t.mapping.map((x: number) => x + 1).length;
}
export function count(t: { mapping: unknown }): number {
  if (t.mapping === null) return 0;
  if (!Array.isArray(t.mapping)) throw Error("invalid slot mapping");
  return t.mapping.length;
}
