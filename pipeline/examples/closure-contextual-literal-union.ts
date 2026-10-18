// A contextual closure parameter at an array literal's records, each given
// the other's member optional at `undefined`:
// `{ a: number; b?: undefined } | { a?: undefined; b: number }`.
export function either(): (number | undefined)[] {
  return [{ a: 1 }, { b: 2 }].map((o) => o.a);
}
