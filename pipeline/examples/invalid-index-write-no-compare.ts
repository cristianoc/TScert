// The mask alone: an index past the length leaves holes (run under Node).
export function wrong(xs: number[], k: number, v: number): number[] {
  if ((k & 0x7fffffff) !== k) throw new RangeError("index");
  xs[k] = v;
  return xs;
}
