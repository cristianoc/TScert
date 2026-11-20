// A fact over a path of two fields whose first a member replaces
// (docs/drafts/framed-acceptance.md, "Milestone 2", the decision's (P)):
// swap writes the field inner, charged at its key, so the component's
// protocol is any at a part of the path's first field and the region of
// h.inner.flags is read unprotected; the fact across the visit is
// refused. A visitor calling swap(h) makes the walker read past the new
// array (NaN under Node, tests/node-runs.mts).
export type H = { readonly flags: readonly number[] };
export type H2 = { readonly inner: H };
type Visitor = (i: number) => Modifies<{ values: "keep"; spines: "any" }, void>;

export function swap(h: { inner: H }): void {
  h.inner = { flags: [] };
}

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
