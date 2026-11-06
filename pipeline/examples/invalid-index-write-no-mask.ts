// The comparison alone: `-1` or `0.5` passes it and the write adds an own
// property no array owns (run under Node).
export function wrong(xs: number[], k: number, v: number): number[] {
  if (k > xs.length) throw new RangeError("index");
  xs[k] = v;
  return xs;
}
