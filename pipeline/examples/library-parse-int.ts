// `parseInt` of a string and a number converts neither by code of the
// client's: within the empty footprint, so a `map` calling it stays dense.
export function hex(digits: string): number {
  return parseInt(digits, 16);
}
export function decimals(texts: string[]): number[] {
  return texts.map((t) => parseInt(t, 10));
}
