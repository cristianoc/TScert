import type { Json, Values } from "@fixture/collections";

// An element read of a generic library interface's array at an
// intersection: the value is the intersection or `undefined`, and a test
// against `undefined` leaves the intersection, whose values are objects.
type Rec = { readonly id: string } & { readonly [key: string]: Json | null };

export function first(values: Values<Rec>): string {
  const v = values.toArray()[0];
  if (v === undefined) return "";
  return v.id;
}
