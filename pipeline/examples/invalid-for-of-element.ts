// An element of a (number | null)[] may be null: it is not a number.
export function sum(xs: readonly (number | null)[]): number {
  let n: number = 0;
  for (const x of xs) {
    n = x;
  }
  return n;
}
