// An array whose elements admit `undefined` may hold a hole at its last
// index: the read there is `undefined`, which the assertion does not
// exclude.
export function last(xs: readonly (string | undefined)[]): string {
  return xs[xs.length - 1] as string;
}
