// Another module of the project merges `toJSON(): undefined` into
// `ReadonlyArray`: the callback's parameter is a read-only array by its
// context alone, which states the hook as well, and is refused.
export function texts(rows: readonly (readonly number[])[]): string[] {
  return rows.map((row) => JSON.stringify(row));
}
