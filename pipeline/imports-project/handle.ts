// A sealed handle (ARITHMETIC.md, "Type invariants"), in the shape of
// pretext's `layout.ts`: the public `PreparedText` is a branded type with no
// field of its own, its representation `PreparedLineBreakData`, the arrays
// the walkers read. Its invariant is stated over the representation's fields
// (`@representation`), which the handle means. `seal` and `open` are
// pretext's casts in and out of the handle; their importers read them at
// their signatures with the invariant's facts.

declare const preparedTextBrand: unique symbol;

/**
 * @invariant this.segmentFlags.length === this.widths.length
 * @representation PreparedLineBreakData
 */
export type PreparedText = {
  readonly [preparedTextBrand]: true;
};

/** @invariant this.segmentFlags.length === this.widths.length */
export type PreparedLineBreakData = {
  widths: number[];
  segmentFlags: Uint8Array;
  label: string;
};

export type InternalPreparedText = PreparedText & PreparedLineBreakData;

export function seal(data: PreparedLineBreakData): PreparedText {
  return data as unknown as PreparedText;
}

export function open(prepared: PreparedText): InternalPreparedText {
  return prepared as InternalPreparedText;
}
