// A conditional type whose result is no union of whole members of the type
// it decides, here `"a"[] | { k: 1 }`, states no selection of that union.
type Wrap<T> = T extends string ? T[] : T;
export function wrap(x: Wrap<"a" | { k: 1 }>): Wrap<"a" | { k: 1 }> {
  return x;
}
