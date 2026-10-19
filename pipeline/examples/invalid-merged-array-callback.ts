// Another module of the project merges `toJSON(): undefined` into `Array`:
// the callback's parameter is an array by its context alone, which states the
// hook as well, and is refused.
export function texts(): string[] {
  return [[1, 2]].map((row) => JSON.stringify(row));
}
