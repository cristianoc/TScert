// Bounds read exactly at the arguments: a string-named key `"0"`, `keyof
// never`, a default naming an earlier parameter, a compound operand, a
// default computed from the arguments, and a parameter whose bound alone
// names another.
type Get<T, K extends keyof T> = T[K];
type Chain<T, U = T, K extends keyof U = keyof U> = K;
type Compound<T, K extends keyof (T & { a: number })> = K;
type Recorded<
  T extends string,
  U = Record<T, number>,
  K extends keyof U = keyof U,
> = K;
type G<T, K extends keyof T> = K;
export function stringKey(x: Get<{ "0": number }, "0">): number {
  return x;
}
export function never(x: keyof { z: Get<never, "a"> }): "z" {
  return x;
}
export function chain(x: keyof { z: Chain<{ a: number }> }): "z" {
  return x;
}
export function compound(x: Compound<{ b: string }, "a">): "a" {
  return x;
}
export function recorded(x: keyof { z: Recorded<"a"> }): "z" {
  return x;
}
export function alone(x: G<{ a: number }, "a">): "a" {
  return x;
}
