// A private member is no key of its class: `"x"` is no key of `C`.
class C {
  private x: number = 1;
  y: number = 2;
}
type G<T, K extends keyof T> = K;
export function f(x: keyof { z: G<C, "x"> }): "z" {
  return x;
}
