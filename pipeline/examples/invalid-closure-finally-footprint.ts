// A closure whose finalizer shortens an array it captures may leave holes
// where `map` expected an element: its footprint keeps no dense prefix, so
// the `map` result may have holes, which `number[]` does not hold (run under
// Node: `wrong(a, a)` pops the array `map` reads, whose result then has no
// element at its last index).
export function wrong(vs: number[], log: number[]): number[] {
  const f = (v: number): number => {
    try {
      return v;
    } finally {
      log.pop();
    }
  };
  return vs.map((v) => f(v));
}
