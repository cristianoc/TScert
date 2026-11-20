// A walker that is no entry, given its cursor by its caller: checked at the
// context of its one known call (the Read-only frames note, (B1) and (B4)
// at known calls), where the slot of c holds the site of total's cursor
// and the slot of visit the token of an arrow reaching seen alone. The
// cursor's site lies outside the visit's reach, so 0 <= c.i and
// c.i < xs.length are kept across it. At an open entry the slot of c would
// hold outside storage, which the visitor's stated effect may change.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

function walk(xs: number[], c: Cursor, visit: Visitor): number {
  c.i = 0;
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    s += xs[c.i]!;
    c.i++;
  }
  return s;
}

export function total(xs: number[]): number {
  const c: Cursor = { i: 0 };
  const seen = { n: 0 };
  return walk(xs, c, () => { seen.n++; });
}
