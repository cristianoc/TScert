// After `x === 1` fails, `x` is 2 or 3: no 1 remains in its set.
export function rest(x: 1 | 2 | 3): number {
  if (x === 1) return 0;
  const one: 1 = x;
  return one;
}
