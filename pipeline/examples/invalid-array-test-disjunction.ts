// Where `Array.isArray(a) || Array.isArray(b)` holds, either may be the
// array: `a` may be the number, whose `length` is `undefined` (run under
// Node: `wrong(1, [2])`), which no number is.
export function wrong(a: number[] | number, b: number[] | number): number {
  if (Array.isArray(a) || Array.isArray(b)) return (a as number[]).length;
  return 0;
}
