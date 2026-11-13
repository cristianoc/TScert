// The local reassigned after the record was built from it: `lists.widths`
// holds the old array, `w` a new empty one, so what `measure` states of
// `lists.widths` says nothing of `w`, and the write past `w`'s end is refused
// (run under Node: `literal([])` writes at index 1 of an empty array,
// leaving a hole).
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
  let w = widths;
  const lists: Lists = { widths: w };
  const at = w.length;
  if (lists.widths.length > 1000) throw new RangeError('index');
  w = [];
  measure(2, lists);
  w[at + 1] = 0;
}
