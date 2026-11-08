// Reads bounded by a quantified precondition over a typed array's elements
// (PROGRAM-TYPING.md, "Quantified clauses"; SOURCE-CONTRACTS.md, "Stated
// library types"): `forall i in segmentItems: …` states of every index below
// the view's typed-array length that its element is a safe integer below
// `hyphenWidths.length`, and `%ByteAt%`'s bounded read states its result the
// element there, so the element bounds a read (pretext's getHyphenRooms,
// rich-inline.ts), also of a view read through a record's field.

/** @requires forall i in segmentItems: safeInteger(segmentItems[i]) && 0 <= segmentItems[i] && segmentItems[i] < hyphenWidths.length */
export function hyphenRooms(hyphenWidths: number[], itemSegments: number[], segmentItems: Int32Array): number[] {
  const rooms: number[] = [];
  for (let i = 0; i < segmentItems.length; i++) {
    const index = segmentItems[i]!;
    rooms.push(i === itemSegments[index] ? 0 : hyphenWidths[index]!);
  }
  rooms.push(0);
  return rooms;
}

export type Flow = { readonly widths: number[]; readonly segmentItems: Uint16Array };

/** @requires safeInteger(k) && 0 <= k && k < flow.segmentItems.length
 * @requires forall i in flow.segmentItems: safeInteger(flow.segmentItems[i]) && 0 <= flow.segmentItems[i] && flow.segmentItems[i] < flow.widths.length */
export function widthOfItem(flow: Flow, k: number): number {
  const { widths, segmentItems } = flow;
  return widths[segmentItems[k]!]!;
}
