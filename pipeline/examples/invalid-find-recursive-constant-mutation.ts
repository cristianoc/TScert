// A `find` callback calling a recursive constant that shrinks the array
// once its recursion ends: the closure's footprint is not the empty one, so
// the callback is `find`'s unrestricted one, its element
// `number | undefined`; the next visit hands it `undefined`.
export function wrong(xs: number[], seen: { value: number }): number {
  const shrink = (n: number, k: number): boolean => {
    if (k > 0) return shrink(n, k - 1);
    seen.value = n;
    xs.pop();
    return false;
  };
  xs.find((n) => shrink(n, 1));
  return seen.value;
}
