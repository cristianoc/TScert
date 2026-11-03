// A guard closure that shortens an array it captures may leave holes where
// `map` expected an element: its footprint keeps no dense prefix, so a `map`
// calling it may give holes, which `boolean[]` does not hold (run under
// Node: `wrong(a, a)` pops the array `map` reads, whose result then has no
// element at its last index).
type A = { k: "a"; v: string };
type B = { k: "b"; w: number };
export function wrong(vs: (A | B)[], log: (A | B)[]): boolean[] {
  const isA = (e: A | B): e is A => {
    log.pop();
    return e.k === "a";
  };
  return vs.map((v) => isA(v));
}
