// A guard that shortens an array it is given may leave holes where `map`
// expected an element: its footprint keeps no dense prefix, so a `map`
// calling it may give holes, which `boolean[]` does not hold (run under
// Node: `wrong(a, a)` pops the array `map` reads, whose result then has no
// element at its last index).
function isNumber(v: string | number, log: string[]): v is number {
  log.pop();
  return typeof v === "number";
}
export function wrong(vs: (string | number)[], log: string[]): boolean[] {
  return vs.map((v) => isNumber(v, log));
}
