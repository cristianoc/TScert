// A module exporting a value binding beside its walker
// (docs/drafts/framed-acceptance.md, "Milestone 2", the read-only positions):
// the binding names none of the module's code, so the interface stays known
// and the walker's framed plan holds, its spine read as protected.
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
export const K: number = 1;
