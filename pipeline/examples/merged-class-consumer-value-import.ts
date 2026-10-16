// A class merged with an interface is one instance contract, every part's
// members: a function consuming an imported `Augmented` reads `m`, which the
// interface adds, and one consuming a local class that declares `m` too. The
// construction site carries the obligation to give the whole contract.
import type { Augmented } from "@fixture/whole";
class D {
  m: number = 1;
}
interface D {
  m: number;
}
export function f(x: Augmented): number {
  return x.m;
}
export function g(x: D): number {
  return x.m;
}
