// Two parameters whose calculus types are equal once readonly is erased
// (docs/drafts/framed-acceptance.md, "Milestone 2", "The crossings an
// entering step records"): h is at a read-only position, w is not; the
// entry records w at the writable type, so only h's crossing protects.
// The fact over h.flags across the visit holds.
export type H = { readonly flags: readonly number[] };
export type W = { flags: number[] };
type Visitor = (i: number) => Modifies<{ values: "keep"; spines: "any" }, void>;

export function walk(h: H, w: W, visit: Visitor): number {
  const n = h.flags.length;
  let s = w.flags.length;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && h.flags.length === n */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += h.flags[i]!;
  }
  return s;
}
