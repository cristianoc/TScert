// A loop's head claims what its cells hold on entry and on every return from
// its body, found by running the body until the head is stable; the update
// runs where the body ends or continues, and the loop is left from its head
// or by a `break`.
export function stable(c: boolean, a: "a", b: "b"): "a" {
  let y: "a" | "b" = a;
  y = a;
  while (c) {
    y = b;
    y = a;
  }
  return y;
}

export function continued(c: boolean): number {
  let x: number;
  let total = 0;
  for (let i = 0; i < 3; i = i + x) {
    x = 2;
    if (c) {
      continue;
    }
    x = 1;
    total = total + x;
  }
  return total;
}

export function broken(c: boolean, a: "a", b: "b"): "a" {
  let y: "a" | "b" = a;
  y = a;
  while (c) {
    y = b;
    if (c) {
      y = a;
      break;
    }
    y = a;
  }
  return y;
}
