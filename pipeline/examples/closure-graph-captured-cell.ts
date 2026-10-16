// A closure writing a captured `let`: after a call that may run it, the
// outer function knows the cell by its contract, and tests it.
export function counter(): number {
  let n: number | null = 0;
  const reset = (): void => {
    n = null;
  };
  n = 1;
  reset();
  return n === null ? 0 : n;
}
