// A key named by an enum member is that member, not its value: TypeScript's
// `keyof` keeps `E.A`, which the fragment states no literal for.
enum E {
  A = "a",
}
export function f(x: keyof { [E.A]: number; b: number }): "a" | "b" {
  return x;
}
