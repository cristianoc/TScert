// A walker that pops a writable parameter's array itself
// (docs/drafts/framed-acceptance.md, "Milestone 2", the natives the realm
// does not model): w.flags.pop() calls a method read from storage, a
// native whose steps are the component's, so the node protocol is any at
// every part of outside storage the call reaches and h.flags.length === n
// across the visit is refused by the protocol. A client passing one record
// as both arguments makes the walker read past its array (NaN under Node,
// tests/node-runs.mts).
export type H = { readonly flags: readonly number[] };
export type W = { flags: number[] };
type Visitor = (i: number) => Modifies<{ values: "keep"; spines: "any" }, void>;
export function walk(h: H, w: W, visit: Visitor): number {
  const n = h.flags.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && h.flags.length === n */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += h.flags[i]!;
    w.flags.pop();
  }
  return s;
}
