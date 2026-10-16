// A standard library global is read as a value only where the overlay states
// each of its call signatures for one: `String`'s is stated for a call alone.
export function texts(xs: readonly number[]): string[] {
  return xs.map(String);
}
