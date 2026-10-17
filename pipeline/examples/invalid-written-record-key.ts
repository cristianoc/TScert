// `keyof Record<string, number>` is `string`: `number` is no key of it.
type G<T, K extends keyof T> = K;
export function f(x: keyof { z: G<Record<string, number>, number> }): "z" {
  return x;
}
