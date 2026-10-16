// A binding pattern steps its source likewise: the first step finds the empty
// array's end, the default grows the array, and `b`'s step finds the iterator
// finished, so `b` is undefined, where a read of position 1 finds 2.
export function defaultGrows(): number | undefined {
  const xs: number[] = [];
  const [a = (xs.push(1, 2), 0), b] = xs;
  return a + (b ?? 100);
}
