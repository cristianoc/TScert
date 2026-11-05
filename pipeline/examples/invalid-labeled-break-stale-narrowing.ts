// The statement after the labeled loop is reached only by `break outer`,
// where `box.v` was tested a string, but `reset()` ran after the test and
// may write a number: TypeScript keeps the narrowing across the call, and
// the function returns a number for its string result.
type Box = { v: string | number };

export function stale(box: Box, reset: () => void): string {
  outer: for (;;) {
    if (typeof box.v === "string") {
      for (;;) {
        reset();
        break outer;
      }
    }
    return "none";
  }
  return box.v;
}
