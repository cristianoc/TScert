// An alias whose equation applies another type to a computed argument is a
// computed alias, read at each reference's arguments: `KeyBox<Entry>` is
// `Box<"stated" | "name">` and `KeyList<Entry>` is
// `readonly ("stated" | "name")[]`.
interface Entry {
  stated: number;
  name: string;
}
interface Box<V> {
  value: V;
}
type KeyBox<T> = Box<keyof T>;
type KeyList<T> = ReadonlyArray<keyof T>;
export function box(b: KeyBox<Entry>): string {
  return b.value === "stated" ? "s" : b.value;
}
export function first(keys: KeyList<Entry>): "stated" | "name" | undefined {
  return keys[0];
}
export function make(): KeyBox<Entry> {
  return { value: "name" };
}
