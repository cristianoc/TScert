// A fact a call's postcondition states of a record's field read of the
// local the record was built from: `lists.widths` and `widths` hold one
// array (the link `lists.widths ≐ widths`), so the length `measure` states of
// `lists.widths` bounds the write to `widths` (ARITHMETIC.md, "Linear facts").
type Lists = { /** @stable */ readonly widths: number[] };
/**
 * @requires safeInteger(n) && 0 <= n && n <= 1000
 * @requires 0 <= p.widths.length && p.widths.length <= 1000
 * @ensures p.widths.length === old(p.widths.length) + n
 */
function measure(n: number, p: Lists): Modifies<{ values: "any"; stores: "grow" }, void> {
  /** @invariant safeInteger(k) && safeInteger(n) && 0 <= k && k <= n && p.widths.length === old(p.widths.length) + k */
  for (let k = 0; k < n; k++) p.widths.push(k);
}
/** @requires 0 <= widths.length && widths.length <= 1000 */
export function literal(widths: number[]): void {
  const lists: Lists = { widths };
  const at = widths.length;
  if (lists.widths.length > 1000) throw new RangeError('index');
  measure(2, lists);
  widths[at + 1] = 0;
}
