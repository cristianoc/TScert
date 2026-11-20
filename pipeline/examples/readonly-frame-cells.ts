// An element fact over the cells of a read-only parameter's array
// (docs/drafts/framed-acceptance.md, "Milestone 2", the decision): a
// visitor letting every value change keeps the spines, so the fact over
// the cells of items, a local alias of h.items, holds across the visit
// only where those cells are read as protected, their prefix the spine
// they are read from and the alias's read of h's field items.
export type H = { readonly items: readonly number[]; readonly widths: readonly number[] };
type Visitor = (i: number) => Modifies<{ values: "any"; spines: "keep" }, void>;

/** @requires forall k in h.items: safeInteger(h.items[k]) && 0 <= h.items[k] && h.items[k] < h.widths.length */
export function walk(h: H, visit: Visitor): number {
  const items = h.items;
  const widths = h.widths;
  const n = items.length;
  let s = 0;
  /** @invariant safeInteger(i) && 0 <= i && safeInteger(n) && items.length === n && forall k in items: safeInteger(items[k]) && 0 <= items[k] && items[k] < widths.length */
  for (let i = 0; i < n; i++) {
    visit(i);
    s += widths[items[i]!]!;
  }
  return s;
}
