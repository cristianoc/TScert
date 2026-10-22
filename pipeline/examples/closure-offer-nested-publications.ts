// A named closure offered a callback's signature at a narrower element,
// returning a guard closure: its body is claimed per signature, and the
// nested closure's own signatures are the function's, stated once.
export function mapped(xs: number[]): unknown[] {
  const go =
    (t: number | string): unknown =>
    (x: unknown): x is number =>
      false;
  return xs.map(go);
}
