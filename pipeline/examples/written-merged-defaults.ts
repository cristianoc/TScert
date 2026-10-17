// A merged generic interface whose defaults another declaration states: `I`
// is `I<{ a: number }, "a">`.
interface I<T, K extends keyof T> {
  a: K;
}
interface I<T = { a: number }, K extends keyof T = keyof T> {
  b: T;
}
export function f(x: keyof { z: I }): "z" {
  return x;
}
export function g(x: I): number {
  return x.b.a;
}
