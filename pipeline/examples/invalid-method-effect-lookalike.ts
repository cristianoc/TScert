// An object literal whose method pops the array it is handed, passed where
// an interface whose member states the empty footprint is expected: the
// subsumption compares the effects (run under Node: a hole).
export interface Take {
  take(
    xs: number[],
    x: number,
  ): Within<{ value: "keep"; store: "keep" }, number>;
}

export function taken(t: Take, xs: number[]): number[] {
  const r: number[] = xs.map((x) => t.take(xs, x));
  return r;
}

export function wrong(xs: number[]): number[] {
  return taken(
    {
      take(ys: number[], x: number): number {
        ys.pop();
        return x;
      },
    },
    xs,
  );
}
