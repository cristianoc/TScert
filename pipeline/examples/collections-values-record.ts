// A record's meet with DepSafe is not empty in the model: an object type
// names only the keys it constrains, so `{ total: number } & DepSafe` is the
// record with Managed's symbol key too. Its field is read as the record's, in
// a method and in a module function, and the value is Managed.
import type { Managed, Values } from "@fixture/collections";
class Totals {
  of(values: Values<{ total: number }>): number {
    return values.getUnique().total;
  }
}
export function total(values: Values<{ total: number }>): number {
  return new Totals().of(values) + values.getUnique().total;
}
export function managed(values: Values<{ total: number }>): Managed {
  return values.getUnique();
}
