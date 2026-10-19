// Another module of the project merges `label(): string` into
// `ArrayIterator`, the type of an array's `values()`: refused at the unit's
// first array.
export function count(xs: number[]): number {
  let n = 0;
  for (const _ of xs.values()) n++;
  return n;
}
