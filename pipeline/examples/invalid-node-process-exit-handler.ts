// `process.exit` runs the `exit` listeners synchronously, and one may change
// the array `map` reads and then throw into the caller (run under Node: the
// handler goes on and the result has a hole): the call states no effect, on
// its throw too.
export function rows(xs: number[]): number[] {
  return xs.map((x) => {
    try {
      process.exit(0);
    } catch {
      return x;
    }
  });
}
