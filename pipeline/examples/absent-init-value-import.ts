// An imported function of a module whose top-level code calls a function the
// gate refuses: the module is lowered with its top-level code left out, and
// `kept`, which reads none of the names that code binds, is read at the
// entry its own unit establishes. The `map` callback calling it keeps the
// array, and the result is dense.
import { kept } from "@fixture/partial-init";
export function incremented(xs: number[]): number[] {
  return xs.map((x) => kept(x));
}
