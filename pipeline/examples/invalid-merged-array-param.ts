// Another module of the project merges `toJSON(): undefined` into `Array`: a
// `number[]` here states a hook, so the annotation is not the standard
// library's array and is refused.
export function text(xs: number[]): string {
  return JSON.stringify(xs);
}
