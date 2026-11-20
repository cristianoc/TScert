// A fact read on a framed call's exceptional edge (docs/drafts/framed-acceptance.md,
// "Milestone 2", the slot copies across a handler): the handler binds the
// thrown value in front of the slots, which keep their copies, so the spine
// of h.flags is read as protected on the handler's edge too.
export type H = { readonly flags: readonly number[] };
type Visitor = (i: number) => Modifies<{ values: "keep"; spines: "any" }, void>;

export function walk(h: H, visit: Visitor): number {
  const n = h.flags.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && h.flags.length === n */
  for (let i = 0; i < n; i++) {
    try {
      visit(i);
    } catch {
      s += h.flags[i]!;
    }
  }
  return s;
}
