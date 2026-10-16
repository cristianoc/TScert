// A fully annotated class with a static block: the block is code, not
// swept.
export function f(x: keyof { z: import("@fixture/whole").WithStatic }): "z" {
  return x;
}
