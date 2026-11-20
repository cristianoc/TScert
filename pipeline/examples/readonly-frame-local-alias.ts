// The Read-only frames note's opening module (Example "The module above",
// docs/drafts/readonly-frames-note/note.tex): a walker reads a handle's
// widths through a local alias, const w = h.widths, across a visitor. The
// alias's slot holds the read of widths from h, at a read-only position
// (docs/drafts/framed-acceptance.md, "Milestone 2", the slot copies), so
// the spine of w is read as protected and i < w.length holds across the
// visit.
export type H = { readonly widths: readonly number[] };
type Visitor = () => Modifies<{ values: "keep"; spines: "any" }, void>;

export function walk(h: H, visit: Visitor): number {
  const w = h.widths;
  const n = w.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && w.length === n */
  for (let i = 0; i < n; i++) {
    visit();
    s += w[i]!;
  }
  return s;
}
