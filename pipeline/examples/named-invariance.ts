// A mutable array is invariant in its element: `number[]` is no
// `(number | string)[]`, which TypeScript admits.
export function widen(xs: number[]): (number | string)[] {
  return xs;
}
