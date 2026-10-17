// A string-named key is no number: `0` is no key of `{ "0": number }`,
// whose key is the string `"0"`.
type Get<T, K extends keyof T> = T[K];
export function f(x: keyof { z: Get<{ "0": number }, 0> }): "z" {
  return x;
}
