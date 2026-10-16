// A Serializable literal frozen with deepFreeze's explicit type argument:
// inferred from the literal, T would be its record type, whose meet with
// DepSafe's primitive arms TypeScript keeps and cannot index.
import { deepFreeze, type Json } from "@fixture/collections";
type Serializable<T> = T & { readonly [key: string]: Json };
type Todo = Serializable<{ readonly title: string; readonly done: boolean }>;

export function frozen(): Todo {
  return deepFreeze<Todo>({ title: "x", done: false });
}
