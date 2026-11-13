// An import of a function whose unit assumes its module cells apart at its
// entry (pretext's line-breaks.ts `unpackClasses`, read by prepare.ts's
// `readScriptRuns`, `spaceSharesScriptRun`, `getUnspacedGraphemes` and
// analysis.ts's `removeSkippableSegmentBreaks` through their callees): the
// separation names the closure's own captured cells, which no caller
// changes, so the function is laid out and its interface entry published.
// `classCount`, read at its certified footprint, which writes no store of
// the caller's, keeps the fact `i < xs.length` across its call.
import { classCount } from "@fixture/module-cells";

export function widest(xs: number[]): number {
  let widest = 0;
  for (let i = 0; i < xs.length; i++) {
    const limit = classCount();
    if (xs[i]! <= limit && xs[i]! > widest) widest = xs[i]!;
  }
  return widest;
}
