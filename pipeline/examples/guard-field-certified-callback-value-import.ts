// A guard on a field holding an array beside null or a number, a `forEach`
// whose callback calls an imported function its module's run certifies at
// the empty footprint, then the field's reread: the callback keeps the heap,
// so the call keeps what the guard found. The twin of
// invalid-guard-field-unstated-callback-value-import, whose import states no
// effect.
import { twice } from "@fixture/certified";

type Value = null | number | readonly Value[];
type Row = { readonly context: Value };
export function count(t: Row, seen: Value, size: number): number {
  const labels = (v: Value) => twice(size);
  if (!Array.isArray(seen) || !Array.isArray(t.context)) return 0;
  seen.forEach(labels);
  t.context.forEach(labels);
  return t.context.length;
}
