// The bound is another array's: the write leaves holes in a shorter one (run
// under Node).
export function wrong(
  xs: number[],
  ys: number[],
  k: number,
  v: number,
): number[] {
  if ((k & 0x7fffffff) !== k || k > ys.length) throw new RangeError("index");
  xs[k] = v;
  return xs;
}
