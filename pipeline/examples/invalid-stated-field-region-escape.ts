// A body writing outside its field region: the frame names `c.i`, and the
// write `h.extras = []` is no part of it, so `moveTo`'s frame is refused.
// A caller relying on it reads `undefined` (run under Node: `pair` returns
// `NaN`).
type Cursor = { i: number };
export type H = { readonly widths: readonly number[]; extras: number[] | null };

/** @requires safeInteger(j)
 * @ensures safeInteger(c.i) && c.i === j */
function moveTo(c: Cursor, h: H, j: number): Modifies<{ "c.i": "scalar" }, void> {
  c.i = j;
  if (h.extras === null) h.extras = [];
}

/** @requires h.extras === null || h.extras.length === h.widths.length */
export function pair(h: H): number {
  const c: Cursor = { i: 0 };
  if (h.widths.length < 2) return 0;
  moveTo(c, h, 1);
  return h.widths[c.i]! + (h.extras === null ? 0 : h.extras[c.i]!);
}
