// Bounds pattern P2: growth by a known count across a callee.
// Fact: widths.length = old(widths.length) + n after `measure(lists, n)`, so
// the loop keeps widths.length = j + 10 <= flags.length at the read.
// Pretext: rich-inline.ts prepareRichInline (30 sites, the lists
// measureAnalysis appends to); prepare.ts measureAnalysis (1).
// Gap: the clause language states no two-state postcondition (`old(…)`), and
// the callee's frame bounds its growth from below only, so after the call
// the list's length has no upper bound.
type Lists = { /** @stable */ readonly widths: number[] };

/** @requires safeInteger(n) && 0 <= n && n <= 1000 */
function measure(lists: Lists, n: number): Modifies<{ values: "any"; stores: "keep"; "lists.widths[*]": "any" }, void> {
  for (let k = 0; k < n; k++) lists.widths.push(k);
}

/** @requires safeInteger(cap) && 0 <= cap && cap <= 100000 */
export function grown(cap: number): number {
  const widths: number[] = [];
  const lists: Lists = { widths };
  const flags = new Uint8Array(cap);
  let s = 0;
  /** @invariant safeInteger(j) && 0 <= j && safeInteger(cap) && widths.length <= j && j <= cap */
  for (let j = 0; j + 10 <= cap; j += 10) {
    measure(lists, 10);
    s += flags[widths.length - 1]!;
  }
  return s;
}
