// An application omitting its argument obliges the default, read as the
// declaration reader reads `any`, `unknown`, to meet the bound.
type Key<T extends string = any> = keyof { a: T };
export function f(x: Key): "a" {
  return x;
}
