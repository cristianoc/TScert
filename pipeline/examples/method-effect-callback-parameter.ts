// A parameter whose function type states the empty footprint: `map` called
// with it is dense, and a caller passes an arrow its code is certified at
// that statement.
export function mapped(
  xs: number[],
  f: (x: number) => Within<{ value: "keep"; store: "keep" }, number>,
): number[] {
  const r: number[] = xs.map((x) => f(x));
  return r;
}

export function doubled(xs: number[]): number[] {
  return mapped(
    xs,
    (x: number): Within<{ value: "keep"; store: "keep" }, number> => x * 2,
  );
}
