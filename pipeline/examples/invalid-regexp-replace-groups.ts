// A pattern naming no group passes no `groups` object: the callback's fifth
// parameter is never handed one, so a callback taking it is refused.
export function groups(s: string): object {
  let seen: object = {};
  s.replace(
    /(a)/g,
    (_: string, a: string, at: number, input: string, g: object) => {
      seen = g;
      return a + at + input;
    },
  );
  return seen;
}
