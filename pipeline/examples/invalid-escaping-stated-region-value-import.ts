// An importer calling a function whose body violates its stated `"c.*": "scalar"`
// frame gains neither that frame nor its `@ensures`. Under Node `kept([1])`
// pops `xs` and returns `undefined`.
import { escapingNormalize } from "@fixture/false-stated-region-ensures";

export function kept(xs: number[]): number {
  if (xs.length === 0) return 0;
  const c = { i: 0 };
  escapingNormalize(xs, c);
  return xs[0]!;
}
