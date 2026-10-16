// `test` of a global regex leaves its `lastIndex` where the match ended: the
// callback writes the regex it captures, so it is not heap-preserving, and
// `map` takes its unrestricted overload, whose result may hold holes. The
// write shows: the same line tests true, then false.
const word = /\w+/g;
export function marks(lines: string[]): boolean[] {
  return lines.map((l) => word.test(l));
}
