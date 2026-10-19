// Another module of the project gives `ReadonlyArray` the base `Box` at `T`
// and at `string`: the second `at` is no reviewed contract, and the unit is
// refused at its first array.
export function last(xs: readonly number[]): number | undefined {
  return xs.at(-1);
}
