// A member beside a mapped type's key is type syntax: its key, a call, is
// erased and refused.
declare function key<T extends string>(): "a";
export function f(x: keyof { [K in "b"]: number; [key<any>()]: number }): "b" {
  return x;
}
