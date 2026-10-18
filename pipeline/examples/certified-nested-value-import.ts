// A module's own imports are certified imports too: `quadruple` calls
// `twice`, and `doubledAll` passes it to `map`, each read at the footprint
// its unit's certificate states. They preserve the heap, so the `map`
// callbacks calling them are preserving and the results are dense.
import { doubledAll, quadruple } from "@fixture/outer";
export function quadrupled(xs: number[]): number[] {
  return xs.map((x) => quadruple(x));
}
export function doubledRows(xss: number[][]): number[][] {
  return xss.map((xs) => doubledAll(xs));
}
