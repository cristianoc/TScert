// A field outside Json: every present key of a Serializable value holds Json,
// and `undefined` is not Json, so the literal is not one.
import type { Json } from "@fixture/collections";
type Serializable<T> = T & { readonly [key: string]: Json };
type Todo = Serializable<{
  readonly title: string;
  readonly note: string | undefined;
}>;

export function todo(): Todo {
  return { title: "x", note: undefined };
}
