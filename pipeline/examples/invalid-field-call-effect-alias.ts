// A literal's function field, whose inferred contract keeps storage, written
// through an alias with a function that shrinks the list: the write is
// refused, since the field's contract is checked at every write, and the
// `findIndex` through the other reference would hand that function
// `undefined`.
function positive(n: number): boolean {
  return n > 0;
}

export function wrong(xs: number[], seen: { value: number }): number {
  const o = { check: (n: number): boolean => positive(n) };
  const a = o;
  a.check = (n: number): boolean => {
    seen.value = n;
    xs.pop();
    return false;
  };
  xs.findIndex((n) => o.check(n));
  return seen.value;
}
