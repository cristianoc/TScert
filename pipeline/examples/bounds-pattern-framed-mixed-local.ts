// A walker over an array it allocates, its visitor an arrow of total that
// calls the client's function: the visit's segment runs the arrow, the
// component's code, and the client's, outside code. Its callee is no
// function the client passes, so the visit is bounded by the top effect
// outside the component's region and by its charges inside it, where the
// walker's array and cursor lie: c.i < ys.length is kept.
type Visitor = (w: number) => Modifies<{ values: "any"; spines: "grow" }, void>;
type Cursor = { i: number };

function walk(visit: Visitor): number {
  const ys: number[] = [1, 2, 3];
  const c: Cursor = { i: 0 };
  let s = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < ys.length) {
    visit(c.i);
    s += ys[c.i]!;
    c.i++;
  }
  return s;
}

export function total(g: () => void): number {
  return walk(() => { g(); });
}
