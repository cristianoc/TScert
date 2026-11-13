// Bounds pattern P2, the unsafe neighbour of
// `bounds-pattern-known-growth-refused`: each call grows the list by 11 while
// the loop advances by 10, so the read is past the flags' end (run under
// Node: NaN at cap 10). The callee's two-state postcondition counts its
// growth exactly, so the caller's bound fails.
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
export function overgrown(cap: number): number {
  const widths: number[] = [];
  const lists: Lists = { widths };
  const flags = new Uint8Array(cap);
  let s = 0;
  /** @invariant safeInteger(j) && 0 <= j && safeInteger(cap) && 0 <= lists.widths.length && lists.widths.length <= j && j <= cap */
  for (let j = 0; j + 10 <= cap; j += 10) {
    measure(lists, 11);
    s += flags[lists.widths.length - 1]!;
  }
  return s;
}
