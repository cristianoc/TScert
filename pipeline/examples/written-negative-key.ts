// A signed numeric literal is a literal key.
export function f(x: keyof { [-1]: number; a: number }): -1 | "a" {
  return x;
}
