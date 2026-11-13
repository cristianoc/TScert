// The neighbour of `two-state-effect-relation` reading `segs[n - 1]`: after
// the call `segs` may be exactly as long as the list was before it, 2 shorter
// than `n` (under Node, `lastBefore({ widths: [1] }, ["s"])` reads `segs[2]`,
// `undefined` at `string`).
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
  if (n > 2) return segs[n - 1]!;
  return "";
}
