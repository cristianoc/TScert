// An omitted argument whose default computes over another parameter
// (`keyof T`), completed at the written arguments.
type Keys<T, K extends keyof T = keyof T> = K;
type Chain<T, U = T, K extends keyof U = keyof U> = K;
export function keys(x: Keys<{ a: number }>): "a" {
  return x;
}
export function chain(x: Chain<{ a: number }>): "a" {
  return x;
}
