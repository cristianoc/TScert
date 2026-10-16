// A `Map`'s values keep their type: a value of `Map<string, number | null>`
// may be null, so it is no number.
export function values(m: Map<string, number | null>): number {
  let n: number = 0;
  for (const v of m.values()) {
    n = v;
  }
  return n;
}
