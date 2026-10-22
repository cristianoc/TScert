// A literal's function field holding a closure that calls a mutable cell:
// the cell's contract keeps storage, inferred from its initialiser, so
// rebinding it to a function that shrinks the list is refused; the
// `findIndex` would hand that function `undefined`.
function positive(n: number): boolean {
  return n > 0;
}

export function wrong(xs: number[], seen: { value: number }): number {
  let f = positive;
  const o = { check: (n: number): boolean => f(n) };
  f = (n: number): boolean => {
    seen.value = n;
    xs.pop();
    return false;
  };
  xs.findIndex((n) => o.check(n));
  return seen.value;
}
