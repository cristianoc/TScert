// A reference read for its meaning that omits an argument whose default
// computes over another parameter (`keyof U`): the default has no term over
// the parameters, so the reference is refused where it is read.
type Chain<T, U = T, K extends keyof U = keyof U> = K;
export function f(x: Chain<{ a: number }>): "a" {
  return x;
}
