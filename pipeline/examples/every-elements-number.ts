// The instance at number: a guard promising a number, then map at number.
export function successors(xs: readonly (number | string)[]): number[] | null {
  return xs.every((x): x is number => typeof x === "number")
    ? xs.map((x) => x + 1)
    : null;
}
