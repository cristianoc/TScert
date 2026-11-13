// Bounds pattern P13: a typed-array prefix filled with a postfix counter.
// Fact: forall i < count of ends: 0 < ends[i] <= text.length, established by
// the writes ends[count++] = i and returned through a postcondition naming
// the count.
// Pretext: gecko-line-breaks.ts setupClusterBoundaries; prepare.ts
// getUnspacedGraphemes; rich-inline.ts prepareRichInline (5 sites).
// Gap: the prefix fact over the parameter `ends` is not extended across
// `ends[count++] = i` at the loop's back edge, so `fill` cannot state it.
// (The document's program reads with `charCodeAt`, which needs no bound, and
// states no postcondition; here `codePointAt(…)!` needs the fact and `fill`
// states it.)
/** @requires safeInteger(n) && 0 <= n && n <= text.length && ends.length >= n && n <= 2147483647
 * @ensures safeInteger(result) && 0 <= result && result <= n
 * @ensures forall i < result of ends: safeInteger(ends[i]) && 0 < ends[i] && ends[i] <= text.length */
function fill(text: string, ends: Int32Array, n: number): number {
  let count = 0;
  /** @invariant safeInteger(n) && safeInteger(i) && safeInteger(count) && 1 <= i && i <= n + 1 && count === i - 1 && n <= text.length && n <= ends.length && n <= 2147483647
   * @invariant forall k < count of ends: safeInteger(ends[k]) && 0 < ends[k] && ends[k] <= text.length */
  for (let i = 1; i <= n; i++) ends[count++] = i;
  return count;
}

/** @requires text.length <= 2147483647 */
export function first(text: string): number {
  const ends = new Int32Array(text.length);
  const count = fill(text, ends, text.length);
  return count > 0 ? text.codePointAt(ends[0]! - 1)! : 0;
}
