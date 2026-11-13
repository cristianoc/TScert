// A callee whose two-state postcondition is false: it grows the list by
// n + 1, not the n its postcondition states (under Node, a call with n = 2
// on an empty list leaves 3 elements). Refused at its return.
type Lists = { /** @stable */ readonly widths: number[] };

/**
 * @requires safeInteger(n) && 0 <= n && n <= 1000 && 0 <= lists.widths.length
 * @ensures lists.widths.length === old(lists.widths.length) + n
 */
export function measure(lists: Lists, n: number): Modifies<{ values: "any"; stores: "keep"; "lists.widths[*]": "any" }, void> {
  /** @invariant safeInteger(k) && safeInteger(n) && 0 <= k && k <= n && lists.widths.length === old(lists.widths.length) + k */
  for (let k = 0; k < n; k++) lists.widths.push(k);
  lists.widths.push(n);
}
