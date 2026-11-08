// Imported functions stating preconditions: the imported signature
// keeps the clause, and each call here establishes it, `at(xs, j)` below the
// length in a loop and `pairSum(xs, 0)` under a test of the length.
import { at, pairSum } from "@fixture/bounded";

export function total(xs: number[]): number {
  let s = 0;
  for (let j = 0; j < xs.length; j++) s = s + at(xs, j);
  return s;
}

export function firstPair(xs: number[]): number {
  return 1 < xs.length ? pairSum(xs, 0) : 0;
}
