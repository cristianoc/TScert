// A receiver whose contract admits holes (its elements admit undefined):
// every skips a hole, and map at the elements fact's signature for any
// receiver skips it too and leaves it in its result, which may hold holes.
export function marks(xs: (string | undefined)[]): (string | undefined)[] {
  return xs.every((x): x is string => typeof x === "string")
    ? xs.map((x) => x + "!")
    : [];
}
