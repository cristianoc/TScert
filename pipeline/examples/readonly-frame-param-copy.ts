// A walker of a copy of its read-only parameter (docs/drafts/framed-acceptance.md,
// "Milestone 2", the slot copies): const g = h binds the parameter's value,
// so g's slot holds a copy of the argument at a read-only position and the
// spine of g.flags is read as protected across the visit.
export type H = { readonly flags: readonly number[] };
type Visitor = (i: number) => Modifies<{ values: "keep"; spines: "any" }, void>;

export function walk(h: H, visit: Visitor): number {
  const g = h;
  const n = g.flags.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && g.flags.length === n */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += g.flags[i]!;
  }
  return s;
}
