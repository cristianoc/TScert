// The walker of bounds-pattern-unreachable-field in a component
// whose exported type states a `@clients` row with a path key. A framed
// plan reads a component's client obligation by kind
// (docs/drafts/framed-acceptance.md, "Restrictions": `@clients` by kind): a
// path key's part needs the declaration's sites, so the walker's framed
// plan is refused, and its ordinary plan is refused at the read after the
// visit.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

/** @clients { "this.items[*]": "extend" } */
export type Log = { readonly items: number[] };

export function walk(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 };
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    s += xs[c.i]!;
    c.i++;
  }
  return s;
}
