// A `break` leaves the loop with `y` holding "b".
export function bad(c: boolean, a: "a", b: "b"): "a" {
  let y: "a" | "b" = a;
  y = a;
  while (c) {
    y = b;
    if (c) {
      break;
    }
    y = a;
  }
  return y;
}
