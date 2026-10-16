// Where `x === E.A` holds, `x` is `E.A`, 0, not 1.
enum E {
  A,
  B,
}
export function bad(x: E): 1 {
  if (x === E.A) {
    return x;
  }
  return 1;
}
