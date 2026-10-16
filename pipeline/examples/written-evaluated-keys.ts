// Keys TypeScript computes at the arguments: a tuple's, a readonly tuple's,
// a mapped type's, a primitive's.
type G<T, K extends keyof T> = K;
export function tuple(x: keyof { z: G<[number], "0"> }): "z" {
  return x;
}
export function readonlyTuple(x: keyof { z: G<readonly [number], "0"> }): "z" {
  return x;
}
export function mappedKeys(
  x: keyof { z: G<{ [P in 0 | 1]: number }, 0> },
): "z" {
  return x;
}
export function stringKey(x: keyof { z: G<string, "length"> }): "z" {
  return x;
}
export function numberKey(x: keyof { z: G<number, "toFixed"> }): "z" {
  return x;
}
