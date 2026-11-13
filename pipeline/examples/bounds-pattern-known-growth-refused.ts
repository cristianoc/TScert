// Bounds pattern P2: growth by a known count across a callee.
// Fact: lists.widths.length = old(lists.widths.length) + n after
// `measure(lists, n)` (its two-state postcondition, read with the caller's
// state at the call as its entry), so the loop keeps
// lists.widths.length <= j <= flags.length at the read.
// Pretext: rich-inline.ts prepareRichInline (30 sites, the lists
// measureAnalysis appends to); prepare.ts measureAnalysis (1).
type Lists = { /** @stable */ readonly widths: number[] };

/**
 * @requires safeInteger(n) && 0 <= n && n <= 1000 && 0 <= lists.widths.length
 * @ensures lists.widths.length === old(lists.widths.length) + n
 */
function measure(lists: Lists, n: number): Modifies<{ values: "any"; stores: "keep"; "lists.widths[*]": "any" }, void> {
  /** @invariant safeInteger(k) && safeInteger(n) && 0 <= k && k <= n && lists.widths.length === old(lists.widths.length) + k */
  for (let k = 0; k < n; k++) lists.widths.push(k);
}

/** @requires safeInteger(cap) && 0 <= cap && cap <= 100000 */
export function grown(cap: number): number {
  const widths: number[] = [];
  const lists: Lists = { widths };
  const flags = new Uint8Array(cap);
  let s = 0;
  /** @invariant safeInteger(j) && 0 <= j && safeInteger(cap) && 0 <= lists.widths.length && lists.widths.length <= j && j <= cap */
  for (let j = 0; j + 10 <= cap; j += 10) {
    measure(lists, 10);
    s += flags[lists.widths.length - 1]!;
  }
  return s;
}
