// The state a `break` carries past a `finally` is the state after it: the
// write there reaches the loop's exit (TypeScript accepts the annotation).
export function breakThroughFinally(n: number): "a" {
  let x: "a" | "b" = "a";
  let i = 0;
  while (i < n) {
    i = i + 1;
    try {
      break;
    } finally {
      x = "b";
    }
  }
  const y: "a" = x;
  return y;
}
