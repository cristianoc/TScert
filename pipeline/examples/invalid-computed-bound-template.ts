// A template literal alias keeps its bound: `"b"` is no `"a"`.
type Greet<T extends "a"> = `hi ${T}`;
export function f(x: Greet<"b">): "hi b" {
  return x;
}
