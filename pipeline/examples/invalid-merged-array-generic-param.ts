// Another module of the project merges `toJSON(): undefined` into `Array`:
// `Array<number>` here is that merged interface, as `number[]` is, so it
// states a hook and is refused.
export function text(xs: Array<number>): string {
  return JSON.stringify(xs);
}
