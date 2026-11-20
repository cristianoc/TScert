// The walker of bounds-pattern-unreachable-field as a method of an
// exported class. A framed plan's request is a module function with a
// realization (docs/drafts/framed-acceptance.md, "Restrictions": framed
// units are realized units): a method's entering step relates to no
// realized code, so its framed plan is refused, and its ordinary plan is
// refused at the read after the visit, which needs the fact the frame keeps.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

export class Walker {
  walk(xs: number[], visit: Visitor): number {
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
}
