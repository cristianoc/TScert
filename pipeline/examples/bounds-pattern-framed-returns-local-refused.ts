// The walker of bounds-pattern-framed-inner-walker returning an object it
// allocates. walk is no entry, its token outside O, so it is checked at
// the context of its known call; the claim there isolates its run at a
// position of outside code, which reads the realized code's returns
// within O at every context (docs/drafts/framed-acceptance.md,
// "Milestone 3"), and walk returns out, of a local site. Safe: that
// request check refuses the framed plan, and the ordinary plan is refused
// at the read after the visit.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };
type Out = { s: number };

function walk(xs: number[], visit: Visitor): Out {
  const c: Cursor = { i: 0 };
  const out: Out = { s: 0 };
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    out.s += xs[c.i]!;
    c.i++;
  }
  return out;
}

export function countLines(xs: number[]): number {
  const stats = { lines: 0 };
  const o = walk(xs, () => { stats.lines++; });
  return stats.lines + o.s;
}
