// The neighbour of `two-state-invariant-after-statement` whose
// postcondition is false: after the statement before the loop, the body
// pushes one more element than `old(paragraph.widths.length) + to - from`
// (under Node, `measure(0, 2, { widths: [] })` leaves 3 elements). Refused
// at its return.
type Lists = { /** @stable */ readonly widths: number[] };

/**
 * @requires safeInteger(from) && 0 <= from && from <= to && safeInteger(to) && to <= 100000
 * @requires 0 <= paragraph.widths.length && paragraph.widths.length <= 100000
 * @ensures paragraph.widths.length === old(paragraph.widths.length) + to - from
 */
export function measure(from: number, to: number, paragraph: Lists): Modifies<{ values: "any"; stores: "grow" }, void> {
  let s = 0;
  /** @invariant safeInteger(mi) && safeInteger(from) && safeInteger(to) && from <= mi && mi <= to && paragraph.widths.length === old(paragraph.widths.length) + mi - from */
  for (let mi = from; mi < to; mi++) {
    s += 1;
    paragraph.widths.push(s);
  }
  paragraph.widths.push(s);
}
