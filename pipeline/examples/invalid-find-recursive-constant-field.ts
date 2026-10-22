// A constant whose recursion runs through a writable field of a record
// holding it, not through its self entry: the field's contract is its
// annotation, an ordinary arrow, and a function shrinking the array is
// written there, so the callback is `find`'s unrestricted one, its element
// `number | undefined`; the next visit hands `undefined` to that function.
export function wrong(xs: number[], seen: { value: number }): number {
  const visit = (n: number, k: number): boolean =>
    k > 0 ? holder.next(n, k - 1) : false;
  const holder: { next: (n: number, k: number) => boolean } = { next: visit };
  holder.next = (n: number, k: number): boolean => {
    seen.value = n;
    xs.pop();
    return k > 0;
  };
  xs.find((n) => visit(n, 1));
  return seen.value;
}
