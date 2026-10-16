// A `Set<string>`'s elements are strings: spread into a rest of numbers.
function sum(...xs: number[]): number {
  return xs.length;
}

export function spreadSet(s: Set<string>): number {
  // @ts-expect-error A string is no number.
  return sum(...s);
}
