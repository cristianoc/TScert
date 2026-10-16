// `a || b && c` is `a || (b && c)`: where it holds, either `a` did or `b`
// and `c` did, so `x` may still be a number.
type V = null | number | { a: number };

export function mixed(x: V): { a: number } {
  if (typeof x === "number" || (x !== null && typeof x === "object")) return x;
  return { a: 0 };
}
