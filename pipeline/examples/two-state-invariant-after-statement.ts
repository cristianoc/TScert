// A loop invariant's entry term `old(paragraph.widths.length)` read after a
// statement before the loop: the statement moves the slots of the current
// bindings, and the entry term reads the function's entry state at the
// call position of `paragraph`, which no statement moves.
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
}
