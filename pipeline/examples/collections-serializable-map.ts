// A mapper producing Serializable records, passed to EagerCollection.map.
// map is instantiated at `V2 := Serializable<Todo>`, which is not DepSafe; its
// result's `V2 & DepSafe` is the record's meet with DepSafe, a meet row's
// instance.
import type {
  Context,
  EagerCollection,
  Json,
  Mapper,
  Values,
} from "@fixture/collections";
type Serializable<T> = T & { readonly [key: string]: Json };
type Todo = { readonly title: string; readonly done: boolean };

class ToTodo implements Mapper<string, string, string, Serializable<Todo>> {
  mapEntry(
    key: string,
    values: Values<string>,
    _context: Context,
  ): Iterable<[string, Serializable<Todo>]> {
    return [[key, { title: values.getUnique(), done: false }]];
  }
}

export function todos(
  c: EagerCollection<string, string>,
): EagerCollection<string, Serializable<Todo>> {
  return c.map(ToTodo);
}
