// A closure moves the index past the length between the guard and the write
// (run under Node).
export function wrong(xs: number[], v: number): number[] {
  let at = xs.length;
  const skip = (): void => {
    at = at + 2;
  };
  if ((at & 0x7fffffff) !== at || at > xs.length) throw new RangeError("index");
  skip();
  xs[at] = v;
  return xs;
}
