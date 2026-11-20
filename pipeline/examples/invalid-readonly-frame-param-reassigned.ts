// A read-only parameter reassigned to a writable one before the loop
// (docs/drafts/framed-acceptance.md, "Milestone 2", the slot copies):
// after h = w, h's slot holds a copy of w, at no read-only position, so the
// spine of h.flags is read unprotected and the fact across the visit is
// refused. A client popping w.flags under the walker makes it read past it
// (NaN under Node, tests/node-runs.mts).
export type H = { readonly flags: readonly number[] };
export type W = { flags: number[] };
type Visitor = (i: number) => Modifies<{ values: "keep"; spines: "any" }, void>;

export function walk(h: H, w: W, visit: Visitor): number {
  h = w;
  const n = h.flags.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && h.flags.length === n */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += h.flags[i]!;
  }
  return s;
}
