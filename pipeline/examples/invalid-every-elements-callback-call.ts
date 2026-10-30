// map's callback calls a function it is given with the array: an ordinary
// arrow may change anything, so the callback is beyond the empty footprint
// and no signature at the elements fact applies. Under Node the function
// writes null at index 1, and the next visit is handed it.
export function shout(
  xs: (string | null)[],
  f: (ys: (string | null)[]) => void,
): string[] | null {
  return xs.every((x): x is string => x !== null)
    ? xs.map((x) => {
        f(xs);
        return x.toUpperCase();
      })
    : null;
}
