// `Record<Key, number>` over `"a" | "b"` has both fields.
type Key = "a" | "b";
type Pair = Record<Key, number>;
export function bad(): Record<Key, number> {
  return { a: 1 };
}
