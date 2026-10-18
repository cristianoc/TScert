// TypeScript keeps an early `let` narrowed across a call of a closure that
// writes it (run under Node: the string is returned); the call leaves the
// cell at its contract, so the read after it is a number or a string.
export function stale(): number {
  const set = (): void => {
    n = "s";
  };
  let n: number | string = 1;
  if (typeof n === "number") {
    set();
    return n;
  }
  return 0;
}
