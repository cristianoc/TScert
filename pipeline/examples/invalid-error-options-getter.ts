// A getter at `cause`, which `Error` runs through `[[Get]]`: client code that
// shrinks the array `map` visits. Refused at the accessor.
export function wrong(xs: string[]): string[] {
  return xs.map(
    (x) =>
      Error(x, {
        get cause() {
          xs.pop();
          return 0;
        },
      }).message,
  );
}
