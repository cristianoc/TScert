// Functions of a module with a function the gate refuses, `jumped`, that
// read no refused function: `kept`, and `shadowed`, whose parameter of the
// same name is no read of it. Each is read at the footprint its unit's
// certificate states, so the `map` callbacks calling them are preserving and
// the results are dense.
import { kept, shadowed } from "@fixture/partial";
export function incremented(xs: number[]): number[] {
  return xs.map((x) => kept(x));
}
export function shadows(xs: number[]): number[] {
  return xs.map((x) => shadowed(x));
}
