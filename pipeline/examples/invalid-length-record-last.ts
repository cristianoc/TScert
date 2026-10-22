// A record with a `length` and a numeric index signature is no array: its
// `length` says nothing of which numeric keys it owns, and an absent key
// reads `undefined`.
export function last(r: {
  readonly length: number;
  readonly [k: number]: string;
}): string {
  return r[r.length - 1];
}
