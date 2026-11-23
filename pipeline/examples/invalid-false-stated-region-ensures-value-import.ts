// An importer calling a function with a stated regional frame whose `@ensures`
// its module refuses gains no postcondition. Under Node `stepNext([1])`
// returns `undefined`.
import { lyingNormalize } from "@fixture/false-stated-region-ensures";

export function stepNext(xs: number[]): number {
  const c = { i: 0 };
  if (!lyingNormalize(xs, c)) return 0;
  return xs[c.i]!;
}
