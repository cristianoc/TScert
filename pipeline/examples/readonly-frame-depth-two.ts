// A fact over a path of two fields of a read-only parameter
// (docs/drafts/framed-acceptance.md, "Milestone 2", the decision's (P)):
// the region of h.inner.flags reads the field inner, which no code of the
// component writes, so its spine is read as protected across the visit.
export type H = { readonly flags: readonly number[] };
export type H2 = { readonly inner: H };
type Visitor = (i: number) => Modifies<{ values: "keep"; spines: "any" }, void>;

export function walk(h: H2, visit: Visitor): number {
  const n = h.inner.flags.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && h.inner.flags.length === n */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += h.inner.flags[i]!;
  }
  return s;
}
