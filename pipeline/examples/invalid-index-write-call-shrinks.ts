// The right side's call shrinks the array after the guard: the append at the
// old length leaves a hole (run under Node).
export function wrong(
  xs: number[],
  shrink: (xs: number[]) => number,
): number[] {
  const at = xs.length;
  if ((at & 0x7fffffff) !== at || at > xs.length) throw new RangeError("index");
  xs[at] = shrink(xs);
  return xs;
}
