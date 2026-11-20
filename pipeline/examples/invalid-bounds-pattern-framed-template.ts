// The walker of bounds-pattern-framed-inner-walker, its visitor an arrow of
// total converting a client's object in a template literal. The template
// lowers to an addition, which calls no code, so no node of the component
// may call outside code and the visit is bounded by its segment's charges;
// under Node the conversion calls the object's toString, which here pops
// the array. The bound reads the arrow's code as lowered, so walk's verdict
// rests on total's, which is refused at the addition of an object: walk is
// refused by that dependency. Run under Node, total([1, 2, 3], o) with o's
// toString popping the array reads past it (NaN, tests/node-runs.mts).
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

function walk(xs: number[], visit: Visitor): number {
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

export function total(xs: number[], o: { readonly v: number }): number {
  const st = { s: "" };
  return walk(xs, () => { st.s = `${o}`; });
}
