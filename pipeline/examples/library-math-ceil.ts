// `Math.ceil` of a number runs no conversion code and writes nothing: a
// `map` calling it stays dense.
export function pages(sizes: number[], per: number): number[] {
  return sizes.map((n) => Math.ceil(n / per));
}
