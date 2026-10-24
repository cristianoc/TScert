// A stated arrow, in a module constant and in a fresh literal's field: each
// closure's code is certified at its statement over its annotated
// parameters, and `map` callbacks calling them are within the empty
// footprint.
const inc = (n: number): Within<{ value: "keep"; store: "keep" }, number> =>
  n + 1;

const ops = {
  dec: (n: number): Within<{ value: "keep"; store: "keep" }, number> => n - 1,
};

export function incs(xs: number[]): number[] {
  const r: number[] = xs.map((x) => inc(x));
  return r;
}

export function decs(xs: number[]): number[] {
  const r: number[] = xs.map((x) => ops.dec(x));
  return r;
}
