// A handle's invariant across a callback that is never given the handle. The
// walker builds the handle itself from two arrays of equal length and hands
// the visitor only a number, so the visitor cannot change it, and `last` reads
// within `starts`. Safe.
// The visitor's stated effect, `{ values: "any"; spines: "grow" }`, covers
// the handle's fields and lets `widths` grow, so the ordinary plan loses the
// invariant `starts.length === widths.length` for the call `last(h)` after
// the visit. The framed plan reads the read-only frame: the handle's site
// is local and outside the visit's reach, so the invariant is kept, and
// `last(h)` is a known call of a module function, checked by `last`'s
// specification (docs/drafts/framed-acceptance.md, "Milestone 3").
// Pretext: line-break.ts walkPreparedLinesRaw, which passes its prepared
// handle to stepPreparedSimpleLineGeometry after onLine.
/** @invariant this.starts.length === this.widths.length */
type Handle = { widths: number[]; starts: number[] };
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;

function last(h: Handle): number {
  if (h.widths.length === 0) return 0;
  return h.starts[h.widths.length - 1]!;
}

export function walk(visit: Visitor): number {
  const h: Handle = { widths: [3, 4], starts: [0, 3] };
  visit(h.widths.length);
  return last(h);
}
