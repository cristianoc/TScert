// Another module of the project merges `label(): string` into `Iterator`:
// an array's `values()` is read as an `Iterator`, which the merge states a
// member of, and is refused at the unit's first array.
export function count(xs: number[]): number {
  let n = 0;
  for (const _ of xs.values()) n++;
  return n;
}
