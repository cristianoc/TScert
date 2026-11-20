// A walker of a record whose field is read-only and whose array is writable
// (docs/drafts/framed-acceptance.md, "Milestone 2", the protected reading):
// the declared type is not read-only throughout, so h is at no read-only
// position and nothing protects the spine of h.flags. A client popping
// the array under the walker makes it read past it (NaN under Node,
// tests/node-runs.mts).
export type P = { readonly flags: number[] };
type Visitor = (i: number) => Modifies<{ values: "keep"; spines: "any" }, void>;

export function walk(h: P, visit: Visitor): number {
  const n = h.flags.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && h.flags.length === n */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += h.flags[i]!;
  }
  return s;
}
