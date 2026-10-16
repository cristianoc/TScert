// A plain record passed as Json. TypeScript accepts it by its implicit index
// rule; a record type is open, so a value may carry a key of any type, and
// Json's object arm constrains every present key.
import type { Json } from "@fixture/collections";
type Todo = { readonly title: string; readonly done: boolean };

export function asJson(t: Todo): Json {
  return t;
}
