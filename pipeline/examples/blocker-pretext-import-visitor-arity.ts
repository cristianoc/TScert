// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// rich-inline.ts#findWholeLine.
// A closure taking fewer parameters than the visitor an imported function's
// optional parameter states: it is offered the visitor's signature, whose
// first position it binds, and its body is checked there.
import { walkLines, type LineData } from "../pretext-project/line-data.ts";

export function widest(data: LineData): number {
  let max = 0;
  walkLines(data, 100, (width) => {
    if (width > max) max = width;
  });
  return max;
}
