// A template literal bound read at the arguments: `"xb"` is not `x${"a"}`.
type Prefixed<T extends string, K extends `x${T}`> = K;
export function f(x: keyof { z: Prefixed<"a", "xb"> }): "z" {
  return x;
}
