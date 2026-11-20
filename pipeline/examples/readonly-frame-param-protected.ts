// A walker of a record passed read-only throughout (docs/drafts/framed-acceptance.md,
// "Milestone 2", the protected reading): h at a read-only position, so the
// crossing of h at H protects the spine of h.flags, outside storage, and
// h.flags.length === n across a visitor letting every spine change holds
// through the region read as protected (the Read-only frames note, §4.1).
export type H = { readonly flags: readonly number[] };
type Visitor = (i: number) => Modifies<{ values: "keep"; spines: "any" }, void>;

export function walk(h: H, visit: Visitor): number {
  const n = h.flags.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && h.flags.length === n */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += h.flags[i]!;
  }
  return s;
}
