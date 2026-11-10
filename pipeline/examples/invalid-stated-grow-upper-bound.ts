// A call stated `stores: "grow"` keeps no upper bound of a length: `add`
// may lengthen `xs`, so `xs.length <= ys.length` is lost and `ys[n - 1]` may
// be out of bounds (run under Node: `last([], [])` returns `undefined`).
function add(xs: number[]): Modifies<{ values: "any"; stores: "grow" }, void> {
  xs.push(1);
}

export function last(xs: number[], ys: number[]): number {
  if (xs.length > ys.length) return 0;
  add(xs);
  const n = xs.length;
  if (n === 0) return 0;
  return ys[n - 1]!;
}
