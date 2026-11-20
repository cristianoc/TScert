// Tolerant frames, Example "A cursor that may be the record", with the frame
// "c.*" in place of "c.i": the cursor's fields may be the handle's, so no
// rule separates them from `h.extras`, and the reads of `pairAt` are
// refused. `moveTo` also sets an `extras` field holding `null` to `[]`, a
// key-adding write the fragment refuses on its own: with the handle as its
// own cursor, `pairAt` reads `undefined` (run under Node: the sum is `NaN`).
type Cursor = { i: number };
export type H = { readonly widths: readonly number[]; extras: number[] | null };

/** @requires h.extras === null || h.extras.length === h.widths.length */
export function pairAt(h: H, c: Cursor): number {
  if (h.widths.length < 2) return 0;
  moveTo(c, 1);
  return h.widths[c.i]! + (h.extras === null ? 0 : h.extras[c.i]!);
}

/** @requires safeInteger(j)
 * @ensures safeInteger(c.i) && c.i === j */
function moveTo(c: Cursor, j: number): Modifies<{ "c.*": "scalar" }, void> {
  c.i = j;
  const o = c as { i: number; extras?: number[] | null };
  if (o.extras === null) o.extras = [];
}
