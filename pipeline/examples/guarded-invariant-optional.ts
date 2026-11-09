// A guarded invariant through an optional field, in the shape of pretext's
// `walkPreparedComplexLines`: a rich-inline paragraph's handle holds `items`,
// whose `hyphenWidths` is null where its items agree on the hyphen, and
// otherwise one entry per segment; a text's handle has no `items`. The
// invariant `this.items === undefined || this.items.hyphenWidths === null ||
// this.items.hyphenWidths.length === this.widths.length` resolves each path
// past the guards before it: `items` read where it is not `undefined`, its
// `hyphenWidths` where it is not `null` (ARITHMETIC.md, "Guarded
// clauses"). The walker's `const hyphenWidths = items === undefined ? null :
// items.hyphenWidths` states `hyphenWidths === null || hyphenWidths.length
// === widths.length` on each arm, which the read `hyphenWidths[i]!` under
// `hyphenWidths !== null` uses; a caller assuming the invariant establishes
// it at the walker's call.

/** @invariant this.items === undefined || this.items.hyphenWidths === null || this.items.hyphenWidths.length === this.widths.length */
export type Data = {
  widths: number[];
  items?: Items;
};

export type Items = {
  hyphenWidths: number[] | null;
};

/** @requires safeInteger(i) && 0 <= i && i < prepared.widths.length */
export function hyphenAt(prepared: Data, i: number): number {
  const items = prepared.items;
  const hyphenWidths = items === undefined ? null : items.hyphenWidths;
  let width = 0;
  if (hyphenWidths !== null) width = hyphenWidths[i]!;
  return width;
}

export function lastHyphen(prepared: Data): number {
  const n = prepared.widths.length;
  if (n > 0) return hyphenAt(prepared, n - 1);
  return 0;
}
