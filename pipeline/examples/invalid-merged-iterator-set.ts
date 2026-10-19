// Another module of the project merges `label(): string` into `Iterator`:
// a `for...of` over a set steps the host's iterator, read as an `Iterator`,
// and is refused there.
export function count(s: Set<number>): number {
  let n = 0;
  for (const _ of s) n++;
  return n;
}
