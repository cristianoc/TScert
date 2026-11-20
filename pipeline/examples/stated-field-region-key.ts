// Tolerant frames, Example "A cursor that may be the record": `moveTo`'s
// frame names the cursor's field `i` alone, and `pairAt` keeps
// `h.extras === null || h.extras.length === h.widths.length` and
// `2 <= h.widths.length` across the call, also where `c` is `h`: the fields
// `h.extras` and `h.widths` are apart from `c.i` by their keys, the spines by
// their kind.
type Cursor = { i: number };
export type H = { readonly widths: readonly number[]; extras: number[] | null };

/** @requires safeInteger(j)
 * @ensures safeInteger(c.i) && c.i === j */
function moveTo(c: Cursor, j: number): Modifies<{ "c.i": "scalar" }, void> {
  c.i = j;
}

/** @requires h.extras === null || h.extras.length === h.widths.length */
export function pairAt(h: H, c: Cursor): number {
  if (h.widths.length < 2) return 0;
  moveTo(c, 1);
  return h.widths[c.i]! + (h.extras === null ? 0 : h.extras[c.i]!);
}
