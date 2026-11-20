// A walker exported again at a writable type (docs/drafts/framed-acceptance.md,
// "Milestone 2", the read-only positions): walkW is a value naming walk's
// code, which no entry states, so the module's interface is unknown and no
// framed plan reads it. A client calling walkW with a record it pops under
// the walker makes it read past its array (NaN under Node,
// tests/node-runs.mts).
export type H = { readonly flags: readonly number[] };
export type W = { flags: number[] };
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
export const walkW: (h: W, visit: Visitor) => number = walk;
