// The walker of bounds-pattern-unreachable-field in a component whose
// exported type states a `@clients` row changing storage by kind. A framed
// plan reads a client obligation keeping every part
// (docs/drafts/framed-acceptance.md, "Restrictions": a client obligation
// keeping every part): a row letting outside code grow the component's
// arrays is refused, and the walker's ordinary plan is refused at the read
// after the visit.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

/** @clients { spines: "grow" } */
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
