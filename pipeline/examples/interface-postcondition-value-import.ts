// An import of a function whose signature states a postcondition over its
// parameter (pretext's line-breaks.ts `getWebKitLineBreaks`, read by
// analysis.ts's `analyzeText` and `getWebKitParagraphBreaks`): the
// function's unit proves it at its entry frame, so the function is laid
// out as a module row and its interface entry published. `breaksOf`, read
// at its certified footprint, keeps the fact `i < xs.length` across its
// call, and its postcondition bounds the read `b[source.length]!`.
import { breaksOf } from "@fixture/postcondition-row";

export function lastBreaks(xs: number[], source: string): number {
  let total = 0;
  for (let i = 0; i < xs.length; i++) {
    const b = breaksOf(source);
    total += xs[i]! + b[source.length]!;
  }
  return total;
}
