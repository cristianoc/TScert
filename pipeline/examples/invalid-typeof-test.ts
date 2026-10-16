// A failed test does not narrow the other way.
export function wrong(x: number | string): number {
  if (typeof x === "string") {
    return x;
  }
  return 0;
}
