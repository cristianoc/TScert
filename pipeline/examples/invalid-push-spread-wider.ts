// An array of numbers viewed as an array of numbers or strings: a spread of
// strings pushed through the view lands in the array of numbers.
export function wrong(xs: number[], ys: (number | string)[]): number {
  const wide: (number | string)[] = xs;
  wide.push(...ys);
  let last = 0;
  for (const x of xs) last = x;
  return last;
}
