// The Read-only frames note, Example "A walker that is no entry": P22's
// walker, internal, called by the component's export with an arrow of its
// own, as pretext's layout.ts calls walkPreparedLinesRaw with a visitor
// closure. walk is no entry and no closure of it reaches outside code, so
// its token lies outside O and it is checked at the context of its call in
// countLines (the note's (B1) and (B4) at known calls). There the slot of
// visit holds the arrow's token alone, so visit(c.i) is framed; the arrow
// writes stats.lines, and the cursor's site lies outside the call's reach,
// so c.i < xs.length is kept across the visit.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

function walk(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 };
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    s += xs[c.i]!;
    c.i++;
  }
  return s;
}

export function countLines(xs: number[]): number {
  const stats = { lines: 0 };
  walk(xs, () => { stats.lines++; });
  return stats.lines;
}
