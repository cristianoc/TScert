// The literal `5` is no `0 | 1`: the pair built at the bound does not hold
// it (TypeScript rejects the call too).
declare function pick<K extends 0 | 1>(entries: Array<[K, number]>): K;

export function constraintViolated(): 0 | 1 {
  // @ts-expect-error 5 is not assignable to 0 | 1
  return pick([[5, 1]]);
}
