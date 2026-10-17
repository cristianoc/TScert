// A `Pick` within its bound, read at the arguments: `"a"` is a key of
// `{ a: number; b: string }`.
export function f(
  x: keyof { z: typeof import("@fixture/whole").pickedOk.a },
): "z" {
  return x;
}
