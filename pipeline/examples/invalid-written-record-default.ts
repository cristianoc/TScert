// A default TypeScript computes is the contract: `G` is `string`, which `0`
// does not meet.
type G<T = Record<string, number>, K extends keyof T = keyof T> = K;
export function f(x: 0): G {
  return x;
}
