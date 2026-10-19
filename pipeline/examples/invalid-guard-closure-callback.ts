// A guard closure whose body does not establish its promise is refused
// where it is passed as a callback too: `x !== undefined` holds of `null`,
// which is no string.
export function allPresent(xs: (string | null)[]): boolean {
  return xs.every((x): x is string => x !== undefined);
}
