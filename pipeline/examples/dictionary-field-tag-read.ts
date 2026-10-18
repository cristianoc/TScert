// A test of a dictionary's entry is a fact of the entry until a call or a
// write that may alias it: a later read of the entry is of the test's slice
// of what the index holds or `undefined`, the value a missing key reads.
type Json = null | boolean | number | string | Json[] | { [key: string]: Json };
type Target = { [key: string]: Json };
export function size(t: Target): number {
  if (!Array.isArray(t.mapping)) return 0;
  return t.mapping.map((x: Json) => (typeof x === "number" ? x : 0)).length;
}
export function label(t: Target): number {
  if (typeof t.label !== "number") throw Error("invalid label");
  return t.label + 1;
}
// Past a call, the read is of what the index holds or `undefined`.
export function afterCall(t: Target, reset: () => void): Json | undefined {
  if (!Array.isArray(t.mapping)) return [];
  reset();
  return t.mapping;
}
