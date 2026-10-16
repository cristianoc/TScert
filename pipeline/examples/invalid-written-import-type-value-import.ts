// An import type's application keeps its bound: `any`, read as `unknown`, is
// no `string`.
export function f(x: keyof { a: import("@fixture/lib").Bounded<any> }): "a" {
  return x;
}
