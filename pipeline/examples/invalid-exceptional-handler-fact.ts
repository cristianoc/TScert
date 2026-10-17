// A handler starts in the heap the throw left, after whatever the call
// wrote: a fact the guard before the call established of a field does not
// hold there. `clear` empties the field, then throws.
type Box = { v: string | undefined };
function clear(o: Box): number {
  o.v = undefined;
  throw Error("cleared");
}
export function wrong(o: Box): string {
  if (o.v === undefined) return "";
  try {
    clear(o);
  } catch {
    return o.v;
  }
  return "";
}
