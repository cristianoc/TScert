// A spacing argument is outside the stated call, which takes the value only.
export function spaced(xs: number[]): string[] {
  return xs.map((x) => JSON.stringify(x, undefined, 2));
}
