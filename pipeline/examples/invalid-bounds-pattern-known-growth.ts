// Bounds pattern P2, the unsafe neighbour of
// `bounds-pattern-known-growth-refused`: each call grows the list by 11 while
// the loop advances by 10, so the read is past the flags' end (run under
// Node: NaN at cap 10). A two-state postcondition must count the callee's
// growth exactly.
type Lists = { /** @stable */ readonly widths: number[] };

/** @requires safeInteger(n) && 0 <= n && n <= 1000 */
function measure(lists: Lists, n: number): Modifies<{ values: "any"; stores: "keep"; "lists.widths[*]": "any" }, void> {
  for (let k = 0; k < n; k++) lists.widths.push(k);
}

/** @requires safeInteger(cap) && 0 <= cap && cap <= 100000 */
export function overgrown(cap: number): number {
  const widths: number[] = [];
  const lists: Lists = { widths };
  const flags = new Uint8Array(cap);
  let s = 0;
  /** @invariant safeInteger(j) && 0 <= j && safeInteger(cap) && widths.length <= j && j <= cap */
  for (let j = 0; j + 10 <= cap; j += 10) {
    measure(lists, 11);
    s += flags[widths.length - 1]!;
  }
  return s;
}
