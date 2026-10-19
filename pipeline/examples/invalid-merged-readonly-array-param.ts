// Another module of the project merges `toJSON(): undefined` into
// `ReadonlyArray`: a `readonly number[]` here states a hook and is refused.
export function text(xs: readonly number[]): string {
  return JSON.stringify(xs);
}
