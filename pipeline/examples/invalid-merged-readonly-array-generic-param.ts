// Another module of the project merges `toJSON(): undefined` into
// `ReadonlyArray`: `ReadonlyArray<number>` here is that merged interface, as
// `readonly number[]` is, so it states a hook and is refused.
export function text(xs: ReadonlyArray<number>): string {
  return JSON.stringify(xs);
}
