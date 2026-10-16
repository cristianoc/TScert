// A tagged template in a type's computed key is erased, and refused.
declare function tag<T extends string>(s: unknown): "a";
export function f(x: keyof { [tag<any>`a`]: number; a: number }): "a" {
  return x;
}
