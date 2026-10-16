// An array of numbers does not iterate strings.
export function iterate(xs: readonly number[]): Iterable<string> {
  return xs;
}
