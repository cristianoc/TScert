// The read past the bound: with a full view, `at + to - mi` is the view's length,
// read `undefined` at `number` (run under Node: `measure(0, 2, p)` over an empty
// `widths` and two flags pushes `undefined` twice).
type Lists = {
  /** @stable */ readonly widths: number[];
  /** @stable */ readonly segmentFlags: Uint8Array;
};
/**
 * @requires safeInteger(from) && 0 <= from && from <= to && safeInteger(to) && to <= 100000
 * @requires 0 <= paragraph.widths.length && paragraph.widths.length <= 100000 && paragraph.widths.length + to - from <= paragraph.segmentFlags.length
 * @ensures paragraph.widths.length === old(paragraph.widths.length) + to - from
 */
export function measure(from: number, to: number, paragraph: Lists): Modifies<{ values: "any"; stores: "grow" }, void> {
  const sf = paragraph.segmentFlags;
  /** @invariant safeInteger(mi) && safeInteger(from) && safeInteger(to) && from <= mi && mi <= to && paragraph.widths.length === old(paragraph.widths.length) + mi - from && paragraph.widths.length + to - mi <= sf.length */
  for (let mi = from; mi < to; mi++) {
    const at = paragraph.widths.length;
    const f = sf[at + to - mi]!;
    paragraph.widths.push(f);
  }
}
