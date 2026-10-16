// A call in a type's computed key is erased: nothing checks `key`'s bound
// for `any`, so the key is refused.
declare function key<T extends string>(): "a";
export function f(x: keyof { [key<any>()]: number; a: number }): "a" {
  return x;
}
