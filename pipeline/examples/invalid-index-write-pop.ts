// A `pop` between the guard and the write: the old length is past the end
// (run under Node).
export function wrong(xs: number[], v: number): number[] {
  const at = xs.length;
  if ((at & 0x7fffffff) !== at || at > xs.length) throw new RangeError("index");
  xs.pop();
  xs[at] = v;
  return xs;
}
