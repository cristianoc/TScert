// Bounds pattern P1, a handle passed on after its visitor: the visitor's type
// states its effect, `Modifies<{ values: "any"; spines: "grow" }, void>`,
// which keeps a bound on a length but not the handle's invariant
// `flags.length === widths.length`: the visitor may grow `widths` or
// reassign it. `last` relies on the invariant, so the walker cannot pass the
// handle on after a visit. A visitor that pushes onto `widths` makes `last`
// read past the end of `flags` (run under Node: undefined).
// Pretext: line-break.ts walkPreparedLinesRaw passing its prepared handle to
// stepPreparedSimpleLineGeometry after onLine.
/** @invariant this.flags.length === this.widths.length */
export type Handle = { widths: number[]; flags: Uint8Array };
type Visitor = (h: Handle) => Modifies<{ values: "any"; spines: "grow" }, void>;

function last(h: Handle): number {
  if (h.widths.length === 0) return 0;
  return h.flags[h.widths.length - 1]!;
}

export function walk(h: Handle, visit: Visitor): number {
  visit(h);
  return last(h);
}
