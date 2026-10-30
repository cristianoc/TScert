// The guard calls a function it is given with the array: an ordinary arrow
// may change anything, so the guard is beyond the empty footprint and
// every's elements signature does not apply. Under Node the function writes
// null at index 0 once that index was visited, every answers true, and
// map's callback is handed the null.
export function shout(
  xs: (string | null)[],
  f: (ys: (string | null)[]) => void,
): string[] | null {
  return xs.every((x): x is string => {
    f(xs);
    return x !== null;
  })
    ? xs.map((x) => x.toUpperCase())
    : null;
}
