// A handle's invariant over fields the handle does not declare, with no
// `@representation` naming a type that does: its paths resolve through the
// handle's own type, which declares no `widths`, so the clause is refused
// where a function's parameter names the handle.

declare const brand: unique symbol;

/** @invariant this.segmentFlags.length === this.widths.length */
export type PreparedText = {
  readonly [brand]: true;
};

export function identity(prepared: PreparedText): PreparedText {
  return prepared;
}
