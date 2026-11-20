// The walker of bounds-pattern-framed-inner-walker over an array it
// allocates, its visitor an arrow of countLines that writes stats.lines,
// beyond its type's `values: "keep"`. No node of the component may call
// outside code, so the visit is bounded by its segment's charges, the
// arrow's write among them, and the walker's array and cursor lie outside
// the visit's reach: walk's frame check keeps c.i < ys.length. The bound
// reads the arrow's code as lowered, so walk's verdict rests on
// countLines's, which is refused at its call of walk.
type Visitor = (w: number) => Modifies<{ values: "keep"; spines: "any" }, void>;
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

export function countLines(): number {
  const stats = { lines: 0 };
  walk(() => { stats.lines++; });
  return stats.lines;
}
