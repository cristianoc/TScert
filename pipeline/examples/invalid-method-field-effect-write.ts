// A write of a popping function into a field whose contract states the
// empty footprint: the write is checked at the field's contract, the
// statement included (run under Node: a hole).
export function keep(
  n: number,
): Within<{ value: "keep"; store: "keep" }, number> {
  return n;
}

export class Holder {
  f: typeof keep = keep;
}

export function wrong(h: Holder, xs: number[]): number[] {
  h.f = (n: number): number => {
    xs.pop();
    return n;
  };
  const r: number[] = xs.map((x) => h.f(x));
  return r;
}
