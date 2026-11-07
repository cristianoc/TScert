// A handle whose `@representation` names a union, not a record type: a
// value of it has no one record's fields, so the invariant is refused where a
// function's parameter names the handle.

declare const brand: unique symbol;

/**
 * @invariant this.segmentFlags.length === this.widths.length
 * @representation Data
 */
export type PreparedText = {
  readonly [brand]: true;
};

type Data = { widths: number[]; segmentFlags: Uint8Array } | { widths: number[]; segmentFlags: Uint16Array };

export function identity(prepared: PreparedText): PreparedText {
  return prepared;
}
