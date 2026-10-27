// A user guard on a field holding a primitive refines the field reread, as
// one on a field holding an object does: the read's link gives the guard's
// answer to the field's contents.
function isText(value: string | number): value is string {
  return typeof value === "string";
}
export function size(x: { f: string | number }): number {
  if (isText(x.f)) return x.f.length;
  return 0;
}
