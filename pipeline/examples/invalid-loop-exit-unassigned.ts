// The counterpart of blocker-pretext-loop-exit-assigned: a `let` with no
// initializer, one exit of whose `for (;;)` loop does not assign it, read
// after the loop. On an array with no element above the limit the first
// `break` runs before any assignment, and the function returns `undefined`
// where its result is a number (run under Node).
export function firstAbove(xs: number[], limit: number): number {
  let found: number;
  for (let i = 0; ; i++) {
    if (i >= xs.length) {
      break;
    }
    const x = xs[i];
    if (x !== undefined && x > limit) {
      found = i;
      break;
    }
  }
  return found;
}
