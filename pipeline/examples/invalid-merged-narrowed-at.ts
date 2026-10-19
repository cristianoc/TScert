// Another module of the project merges an `at` whose result leaves out
// `undefined` into `ReadonlyArray`: no contract the standard library
// declares, so the unit is refused at its first array.
export function last(xs: readonly number[]): number | undefined {
  return xs.at(-1);
}
