// `KeyBox<Entry>` is `Box<"stated" | "name">`: its value may be "name", so
// an assertion to `Box<"stated">` is refused.
interface Entry {
  stated: number;
  name: string;
}
interface Box<V> {
  value: V;
}
type KeyBox<T> = Box<keyof T>;
export function stated(b: KeyBox<Entry>): "stated" {
  return (b as Box<"stated">).value;
}
export const run = (): "stated" => stated({ value: "name" });
