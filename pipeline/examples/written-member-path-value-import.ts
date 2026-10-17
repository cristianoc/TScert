// A member path through `typeof`: the property is swept with its
// interface's binder, `T extends string`.
export function f(x: keyof { z: typeof import("@fixture/lib").keyed.x }): "z" {
  return x;
}
