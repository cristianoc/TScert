// A plain record-valued collection. TypeScript accepts it by its implicit
// index rule; a record type is open, so a value may carry a key of any type,
// and the record is not within `EagerCollection`'s `V extends Json` bound.
import type { EagerCollection } from "@fixture/collections";
type Todo = { readonly title: string; readonly done: boolean };

export function title(c: EagerCollection<string, Todo>, key: string): string {
  return c.getUnique(key).title;
}
