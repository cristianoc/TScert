// A callback run between the length's read and the element's can empty the
// array: the read is then `undefined`.
export function called(xs: string[], f: () => void): string {
  const n = xs.length;
  f();
  return xs[n - 1];
}
