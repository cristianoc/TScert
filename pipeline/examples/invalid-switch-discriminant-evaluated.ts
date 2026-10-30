// A `switch` with no `case` test still evaluates its discriminant first:
// `typeof x` before `x`'s initialization throws, so the handler runs and
// answers 1, which the result type `0` does not admit (run under Node: 1).
// TypeScript refuses the handler's return too.
export function defaultOnly(): 0 {
  try {
    switch (typeof x) {
      default:
        return 0;
    }
  } catch {
    const one: number = 1;
    return one;
  }
  let x: number = 0;
  return 0;
}
