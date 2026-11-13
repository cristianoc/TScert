// Rule Call's relational context includes the callee's effect: `measure`
// grows every store (`stores: "grow"`), so `segs` is at least as long after
// the call as before it, and its post states the list 2 longer. From
// `|lists.widths| <= |segs|` before the call, the caller reads
// `|lists.widths| - 2 <= |segs|` after it, and `segs[n - 3]` is present.
type Lists = { /** @stable */ readonly widths: number[] };

/**
 * @requires safeInteger(from) && 0 <= from && from <= to && safeInteger(to) && to <= 100000
 * @requires 0 <= paragraph.widths.length && paragraph.widths.length <= 300000
 * @ensures paragraph.widths.length === old(paragraph.widths.length) + to - from
 */
function measure(from: number, to: number, paragraph: Lists): Modifies<{ values: "any"; stores: "grow" }, void> {
  /** @invariant safeInteger(mi) && safeInteger(from) && safeInteger(to) && from <= mi && mi <= to && paragraph.widths.length === old(paragraph.widths.length) + mi - from */
  for (let mi = from; mi < to; mi++) paragraph.widths.push(0);
}

/** @requires 0 <= lists.widths.length && lists.widths.length <= 1000 && lists.widths.length <= segs.length */
export function lastBefore(lists: Lists, segs: string[]): string {
  measure(0, 2, lists);
  const n = lists.widths.length;
  if (n > 2) return segs[n - 3]!;
  return "";
}
