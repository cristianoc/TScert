// A closure recursing through a `let`, a cell, not a constant's self entry:
// the cell is rebound to a function shrinking the array before the `find`,
// whose next visit hands `undefined` to the function the cell then holds.
// The binding is early (its closure reads it), and an early binding whose
// initializer reads it is refused.
export function wrong(xs: number[], seen: { value: number }): number {
  let f = (n: number, k: number): boolean => (k > 0 ? f(n, k - 1) : false);
  const g = f;
  f = (n: number, k: number): boolean => {
    seen.value = n;
    xs.pop();
    return k > 0;
  };
  xs.find((n) => g(n, 1));
  return seen.value;
}
