// Pushing onto an unconfined parameter array that may alias `bag.chunks`
// invalidates `bag`'s quantified element-length invariant.
/** @invariant forall i in this.chunks: this.chunks[i] === null || 1 <= this.chunks[i].length */
type Bag = { chunks: (number[] | null)[] };

export function pushAliased(bag: Bag, target: (number[] | null)[]): Bag {
  target.push([]);
  return bag;
}
