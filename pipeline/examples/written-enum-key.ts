// An enum member with a literal value is a key at that value.
enum E {
  A = "a",
}
export function f(x: keyof { [E.A]: number; b: number }): "a" | "b" {
  return x;
}
