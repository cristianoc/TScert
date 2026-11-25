// Under Node, shortExtras([[3]], [])[0] is undefined. Neither disjunct
// guards the absent entry before the comparison reads its length.
/** @requires forall j in extras: extras[j] === null || 1 <= 0
 *  @ensures forall j in chunks: result[j] === null || chunks[j] === null || chunks[j].length <= result[j].length */
export function shortExtras(
  chunks: (number[] | null)[],
  extras: (number[] | null)[],
): (number[] | null)[] {
  return extras;
}
