// Bounds pattern P1, the supported neighbour of
// `invalid-bounds-pattern-visitor-handle`: the walker reads through locals it
// takes before the visit, and passes the handle on to nothing after it. The
// visitor's effect, `{ values: "any"; spines: "grow" }`, keeps the bound
// `count <= flags.length`, the length of a typed array no visitor changes.
// The relation is a precondition, which binds at entry: a type invariant on
// `Handle` would also bind `h` at the return, which the visit breaks.
export type Handle = { widths: number[]; flags: Uint8Array };
type Visitor = (h: Handle) => Modifies<{ values: "any"; spines: "grow" }, void>;

/** @requires h.flags.length === h.widths.length */
export function walk(h: Handle, visit: Visitor): number {
  const { flags } = h;
  const count = h.widths.length;
  visit(h);
  if (count === 0) return 0;
  return flags[count - 1]!;
}
