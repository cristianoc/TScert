// Two parameters whose calculus types are equal once readonly is erased
// (docs/drafts/framed-acceptance.md, "Milestone 2", "The crossings an
// entering step records"): w is at no read-only position, so the entry
// records it at the writable type and nothing protects the spine of
// w.flags; the fact over w.flags across the visit is refused. A client
// popping w.flags under the walker makes it read past it (NaN under Node,
// tests/node-runs.mts).
export type H = { readonly flags: readonly number[] };
export type W = { flags: number[] };
type Visitor = (i: number) => Modifies<{ values: "keep"; spines: "any" }, void>;

export function walk(h: H, w: W, visit: Visitor): number {
  const n = w.flags.length;
  let s = h.flags.length;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && w.flags.length === n */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += w.flags[i]!;
  }
  return s;
}
