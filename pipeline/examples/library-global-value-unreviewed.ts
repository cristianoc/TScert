// A standard library global is read as a value only where the overlay states
// each of its call signatures for one: `BigInt`'s is stated for a call alone.
export function bigs(xs: readonly number[]): bigint[] {
  return xs.map(BigInt);
}
