// A throw is an outcome only where it happens: the path that does not throw
// still returns a value, and `undefined` is not a number.
function first(x: number | undefined, fail: boolean): number {
  if (fail) {
    throw "no";
  }
  return x as number;
}
