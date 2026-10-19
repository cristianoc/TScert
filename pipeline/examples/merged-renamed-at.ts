// Another module of the project restates `ReadonlyArray`'s `at` under
// another binder and parameter name: the same contract as the standard
// library's, so the merge adds nothing and the array is read as ever.
export function last(xs: readonly number[]): number | undefined {
  return xs.at(-1);
}
