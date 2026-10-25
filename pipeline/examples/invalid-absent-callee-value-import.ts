// An imported module's function calling a function of its module the gate
// refuses is left out with it, and read at the type its declaration states,
// which states no heap effect: the `map` callback calling `relayed` is not
// preserving and the result is sparse. `kept` calls no refused function: it
// is read at the footprint its unit's certificate states, and the result of
// the `map` calling it is dense.
import { kept, relayed } from "@fixture/partial";
export function incremented(xs: number[]): number[] {
  return xs.map((x) => kept(x));
}
export function relays(xs: number[]): number[] {
  return xs.map((x) => relayed(x));
}
