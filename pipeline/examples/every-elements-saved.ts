// The test's result kept in a constant, then tested: the atom conditional on
// it holds where the constant is true.
export function shout(xs: (string | null)[]): string[] | null {
  const all = xs.every((x): x is string => x !== null);
  return all ? xs.map((x) => x.toUpperCase()) : null;
}
