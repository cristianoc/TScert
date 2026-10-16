// A `continue` through a `finally` reaches the loop's head with the
// finally's write, and the loop may end there (TypeScript accepts the
// annotation).
export function continueThroughFinally(n: number): "a" {
  let x: "a" | "b" = "a";
  let i = 0;
  while (i < n) {
    i = i + 1;
    if (i > 1) {
      try {
        continue;
      } finally {
        x = "b";
      }
    }
    x = "a";
  }
  const y: "a" = x;
  return y;
}
