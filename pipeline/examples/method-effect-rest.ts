// A stated closure collecting a rest array: its code is checked at the
// signature its annotation states, statement included, and a `map` callback
// calling it is within the empty footprint.
const sum = (
  ...ns: number[]
): Within<{ value: "keep"; store: "keep" }, number> => ns.length;

export function counts(xs: number[]): number[] {
  const r: number[] = xs.map((x) => sum(x, x));
  return r;
}
