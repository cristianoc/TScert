// Constants whose literal initializers state their types: destructured,
// parenthesized and signed.
export function f(
  x: keyof {
    a: typeof import("@fixture/whole").lm;
    b: typeof import("@fixture/whole").paren;
    c: typeof import("@fixture/whole").plus;
  },
): "a" | "b" | "c" {
  return x;
}
