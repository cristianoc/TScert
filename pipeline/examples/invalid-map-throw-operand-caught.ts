// A map callback throwing an error of unrestricted making into a handler of
// its own, which returns normally: the call's effects reach the callback's
// normal return, and a call shrinking the receiver leaves a hole in the
// mapped array (tests/node-runs.mts).
export function lengths(
  xs: (string | null)[],
  fail: (at: number) => Error,
): number[] {
  return xs.map((x, at) => {
    try {
      if (x === null) throw fail(at);
      return x.length;
    } catch {
      return 0;
    }
  });
}
