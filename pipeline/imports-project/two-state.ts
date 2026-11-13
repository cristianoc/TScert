// A two-state postcondition an importer reads at its established entry:
// `measure` grows `lists.widths` by exactly `n`.
export type Lists = { /** @stable */ readonly widths: number[] };

/**
 * @requires safeInteger(n) && 0 <= n && n <= 1000 && 0 <= lists.widths.length
 * @ensures lists.widths.length === old(lists.widths.length) + n
 */
export function measure(lists: Lists, n: number): Modifies<{ values: "any"; stores: "grow" }, void> {
  /** @invariant safeInteger(k) && safeInteger(n) && 0 <= k && k <= n && lists.widths.length === old(lists.widths.length) + k */
  for (let k = 0; k < n; k++) lists.widths.push(k);
}
