// A record value as Json. A record type is open, so it is not a Json object;
// its intersection with Json's object arm states that every present key holds
// Json. A fresh literal meets it by its exact keys; a value of it is a Json,
// reads its named fields at their types, and is the plain record too.
import type { Json } from "@fixture/collections";
type Serializable<T> = T & { readonly [key: string]: Json };
type Plain = { readonly title: string; readonly done: boolean };
type Todo = Serializable<Plain>;

export function todo(): Todo {
  return { title: "x", done: false };
}

export function asJson(t: Todo): Json {
  return t;
}

export function passed(): Json {
  const accept = (value: Json): Json => value;
  return accept(todo());
}

export function title(t: Todo): string {
  return t.title;
}

export function plain(t: Todo): Plain {
  return t;
}
