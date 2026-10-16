// TypeScript keeps `n` narrowed to 1 across the call, but the call runs the
// closure, which writes null there: the cell is known by its contract only.
export function counter(): number {
  let n: number | null = 0;
  const reset = (): void => {
    n = null;
  };
  n = 1;
  reset();
  return n;
}
