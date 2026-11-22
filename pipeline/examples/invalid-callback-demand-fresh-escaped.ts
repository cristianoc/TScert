// A caller allocation that escapes before the walker call is not apart from
// the walked array: `store(h, v)` makes `h.xs === v`, so the closure popping
// `v` pops the walked array, and `xs[c.i]` reads undefined (NaN under Node).
// The caller's `v` is not confined (it is passed to `store`), so the
// callback's write to it is checked against the demand on `h.xs` and refused.
type Visitor = (i: number) => void;
type Cursor = { i: number };

function walk(xs: number[], visit: Visitor): number {
  const c: Cursor = { i: 0 };
  let sum = 0;
  /** @invariant safeInteger(c.i) && 0 <= c.i */
  while (c.i < xs.length) {
    visit(c.i);
    sum += xs[c.i]!;
    c.i++;
  }
  return sum;
}

function store(h: { xs: number[] }, v: number[]): void {
  h.xs = v;
}

export function bad(h: { xs: number[] }): number {
  const v: number[] = [1];
  store(h, v);
  return walk(h.xs, () => {
    v.pop();
  });
}
