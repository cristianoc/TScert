// An imported function whose module the gate admits is read at the footprint
// its own unit's certificate states: `twice` and `label`, the latter calling a
// function of its module, preserve the heap, and `tally` pushes onto the
// array it is given, which keeps every array's dense prefix; `unwrap` reads a
// field of a bounded interface's application. The `map`
// callbacks calling them are preserving, and the results are dense.
import { label, tally, twice, unwrap, type Bounded } from "@fixture/certified";
export function doubled(xs: number[]): number[] {
  return xs.map((x) => twice(x));
}
export function labels(xs: number[]): string[] {
  return xs.map((x) => label(x));
}
export function tallies(xs: number[], seen: number[]): number[] {
  return xs.map((x) => tally(seen, x));
}
export function values(bs: Bounded<number>[]): number[] {
  return bs.map((b) => unwrap(b));
}
