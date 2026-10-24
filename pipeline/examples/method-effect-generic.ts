// A generic method stating the empty footprint, at each instance its
// binders take: a `map` callback calling it at `number` is within the empty
// footprint.
export class Pick {
  first<T>(
    xs: readonly T[],
    fallback: T,
  ): Within<{ value: "keep"; store: "keep" }, T> {
    const [x] = xs;
    return x === undefined ? fallback : x;
  }
}

export function firsts(p: Pick, xss: number[][]): number[] {
  const r: number[] = xss.map((xs) => p.first(xs, 0));
  return r;
}
