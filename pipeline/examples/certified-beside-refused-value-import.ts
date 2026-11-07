// A certified import beside a refused one of the same module (pretext's
// layout.ts reads `normalizeMaxWidth` beside `countPreparedLines`): the
// module run refused at `measured` withdraws that read alone, so the call of
// `normalize`, read at its certified footprint, which writes nothing, keeps
// the fact `i < xs.length`, and `xs[i]!` reads below the length after it.
import { measured, normalize } from "@fixture/beside-refused";

export function widest(xs: number[], width: number): number {
  let widest = 0;
  for (let i = 0; i < xs.length; i++) {
    const limit = normalize(width);
    if (xs[i]! <= limit && xs[i]! > widest) widest = xs[i]!;
  }
  return widest + measured(xs);
}
