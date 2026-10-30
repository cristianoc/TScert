// A negated test returns early; the fact holds after it, on its false edge.
export function shout(xs: (string | null)[]): string[] | null {
  if (!xs.every((x): x is string => x !== null)) return null;
  return xs.map((x) => x.toUpperCase());
}
