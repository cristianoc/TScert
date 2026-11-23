// An imported generic function from a module with a body carries no uncertified
// `@ensures`: `lyingGeneric` sets `c.i = xs.length`, so `read([1])` returns
// `undefined` under Node and is refused.
import { lyingGeneric } from "@fixture/false-stated-region-ensures";

export function read(xs: number[]): number {
  if (xs.length === 0) return 0;
  const c = { i: 0 };
  lyingGeneric(xs, c, undefined);
  return xs[c.i]!;
}
