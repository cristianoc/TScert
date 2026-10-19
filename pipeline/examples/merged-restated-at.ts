// Another module of the project restates `ReadonlyArray`'s `at` exactly as
// the reviewed signature spells it: the reviewed contract, so `at` is read
// as ever.
export function last(xs: readonly number[]): number | undefined {
  return xs.at(-1);
}
