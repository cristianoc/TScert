// A `let` found equal to `null` holds null until it is written: a call of a
// closure assigning it ends the refinement, which TypeScript keeps. Under
// Node, `reset()` returns 1 from a function typed to return null.
export function reset(): null {
  let held: unknown = null;
  const write = (): void => {
    held = 1;
  };
  if (held === null) {
    write();
    return held;
  }
  return null;
}
