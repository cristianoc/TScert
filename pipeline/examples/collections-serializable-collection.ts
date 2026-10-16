// A record-valued collection: its values meet `EagerCollection`'s and
// `Mapper`'s `V extends Json` bounds as Serializable records.
import type {
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
  ): Iterable<[string, Serializable<Todo>]> {
    return [[key, { title: values.getUnique(), done: false }]];
  }
}

export function mapped(
  values: Values<string>,
): Iterable<[string, Serializable<Todo>]> {
  return new ToTodo().mapEntry("k", values);
}

export function title(
  c: EagerCollection<string, Serializable<Todo>>,
  key: string,
): string {
  return c.getUnique(key).title;
}
