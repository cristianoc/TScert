// An imported function whose module the gate admits is read at the footprint
// its own unit's certificate states: `twice` and `label`, the latter calling a
// function of its module, preserve the heap, and `tally` pushes onto the
// array it is given, which keeps every array's dense prefix; `unwrap` reads a
// field of a bounded interface's application, and `unwrapped` one through a
// generic interface applying it at its own parameter. The `map`
// callbacks calling them are preserving, and the results are dense.
import {
  label,
  tally,
  twice,
  unwrap,
  unwrapped,
  type Bounded,
  type Wrapped,
} from "@fixture/certified";
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
export function innerValues(ws: Wrapped<number>[]): number[] {
  return ws.map((w) => unwrapped(w));
}
