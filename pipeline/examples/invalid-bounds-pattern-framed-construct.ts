// The walker of bounds-pattern-framed-inner-walker, its visitor an arrow of
// total constructing a client's class. The construction calls outside code,
// so the visit's segment may run outside code; its callee is no argument's
// own value at an entry, so the callback row does not bound it, and the visit
// is bounded by the top effect, which may shrink the client's array: the
// read after the visit is refused. Run under Node, total([1, 2, 3], K) with
// K's constructor popping the array reads past it (NaN,
// tests/node-runs.mts).
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

export function total(xs: number[], K: new () => object): number {
  return walk(xs, () => { new K(); });
}
