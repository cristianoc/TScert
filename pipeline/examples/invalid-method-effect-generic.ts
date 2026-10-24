// A statement on a generic method: a closure's code is checked at the
// binder bounds its claim states, which need not cover its own, so no
// certification covers its whole domain.
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
