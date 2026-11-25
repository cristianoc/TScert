// A `.push()` on a locally allocated array modifies only the confined array
// itself, so quantified invariants on a parameter object outside the confined
// set survive the loop without explicit apartness.
/** @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length */
type Bag = { chunks: (number[] | null)[] };

export function collectLengths(bag: Bag): { bag: Bag; lengths: number[] } {
  const lengths: number[] = [];
  for (let i = 0; i < bag.chunks.length; i++) {
    const c = bag.chunks[i];
    lengths.push(c === null ? 0 : c.length);
  }
  return { bag, lengths };
}
